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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_tables MallocInv_steps.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Steps2.
  Context {R : Type}.
  Variable A : astate.
  Hypothesis HW : WF A.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma ts_lhu_fact : forall s a v (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> has A (FCT a 2 v) -> 0 <= v < 2^16 ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_lhu (Z_to_bv 64 a) ;; k x) s) P.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros s a v k P HR HWn Hf Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3.
    destruct (rep_read A (ms_mem s) HR a 2 v Hf ltac:(llia) ltac:(ceil; cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    eapply ts_lhu; [apply acc_ok_heap; [exact HWn | llia | llia | cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs v); [exact Hk|]. rewrite Hval. apply Z.mod_small. change (2^(8*Z.of_nat 2)) with (2^16). llia.
  Qed.

  Lemma ts_ld_fact : forall s a v (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> has A (FCT a 8 v) -> 0 <= v ->
    tsafe (k (Z_to_bv 64 v) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 a) ;; k x) s) P.
  Proof using HW MLok. pu_keep (HW, MLok).
    intros s a v k P HR HWn Hf Hv Hk.
    destruct (has_addr A HW _ Hf) as (H1 & H2 & H3 & _). cbn in H1, H2, H3.
    destruct (rep_read A (ms_mem s) HR a 8 v Hf ltac:(llia) ltac:(ceil; cbn; llia) ltac:(llia)) as (bs & Hrd & Hl & Hval).
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | cbn; llia] | exact Hrd |].
    rewrite (le_val_Z bs (v mod 2^64)); [rewrite ZZ_mod; exact Hk|]. rewrite Hval. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_ld_ctx_nn : forall s ck (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> cvalid ck -> clen ck = 8 -> 0 <= a_ctx A ck ->
    tsafe (k (Z_to_bv 64 (a_ctx A ck)) s) P ->
    tsafe ((x <- m_ld (Z_to_bv 64 (caddr ck)) ;; k x) s) P.
  Proof using MLok. pu_keep (MLok).
    intros s ck k P HR HWn Hk Hlen Hv Hk'.
    destruct (rep_read_ctx A (ms_mem s) ck HR Hk Hv) as (bs & Hrd & Hl & Hval).
    rewrite Hlen in *. change (Z.to_nat 8) with 8%nat in *.
    pose proof (ctx_slot_range ck Hk) as (C1 & C2 & C3). unfold LOCKA, CTX_END in *.
    eapply ts_ld; [apply acc_ok_heap; [exact HWn | llia | llia | ceil; llia] | exact Hrd |].
    rewrite (le_val_Z bs (a_ctx A ck mod 2^64)); [rewrite ZZ_mod; exact Hk'|]. rewrite Hval. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ts_lw_meta32 : forall s ma mt fl (k : word -> M R) P,
    Rep A (ms_mem s) -> WIN s -> a_meta A ma = Some mt -> mlen fl = 4 -> 0 <= mt_f mt fl < 2^32 ->
    tsafe (k (w32 (mt_f mt fl)) s) P ->
    tsafe ((x <- m_lw (Z_to_bv 64 (ma + moff fl)) ;; k x) s) P.
  Proof using HW MLok. pu_keep (HW, MLok). intros. eapply ts_lw_meta; eauto. Qed.
End Steps2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w32_fields : forall w, 0 <= w ->
  Z.land w 31 = w_last w /\ (w * 2^52) mod 2^64 / 2^58 = w_sc w /\ w / 2^12 = w_maplen w.
Proof using Type. pu_keep tt.
  intros w Hw. unfold w_last, w_sc, w_maplen. split; [apply land_31; llia|]. split; [| reflexivity].
  change (2^64) with (2^12 * 2^52). rewrite Z.mul_mod_distr_r by llia.
  change (2^58) with (2^6 * 2^52). rewrite Z.div_mul_cancel_r by llia.
  pose proof (Z.div_mod w 4096 ltac:(llia)) as E. pose proof (Z.mod_pos_bound w 4096 ltac:(llia)) as B.
  set (a := w / 4096) in *. set (b := w mod 4096) in *.
  change (2^12) with 4096. change (2^6) with 64. fold b.
  rewrite E. replace (4096 * a + b) with (a * 64 * 64 + b) by llia.
  rewrite Z.div_add_l by llia. rewrite Z.add_comm, Z.mod_add by llia.
  symmetry. apply Z.mod_small. split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section GetMeta.
  Context {R : Type}.
  Variables (A : astate) (s : mstate).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z) (st : slot_st) (soff p : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some st.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hst : (exists n, st = SLive soff n) \/ (exists ch, st = SNested ch /\ soff = 0).
  Hypothesis Hp : p = slot_start mt i + 16 * soff.

  Let S := mt_stride mt.
  Let Mb := mt_mem mt.
  Let p0 := Mb + 16 + i * S.

  (* [comment removed for export] *)
  Lemma slot_hdr_facts : exists c, 0 <= c <= 6 /\
    has A (FCT (p - 4) 1 0) /\ has A (FCT (p - 3) 1 (i + 32 * c)) /\ has A (FCT (p - 2) 2 ((p - Mb - 16) / 16)).
  Proof using HW Hi Hi0 Hma Hp Hr Hst p0. pu_keep (HW, Hi, Hi0, Hma, Hp, Hr, Hst, p0).
    assert (G : forall f, In f (slot_fields mt (Z.of_nat (Z.to_nat i)) st) -> has A f).
    { intros f Hf. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
      exists (Z.to_nat i), st. split; [exact Hi | exact Hf]. }
    rewrite Z2Nat.id in G by llia.
    unfold slot_fields, slot_fields_g in G. fold Mb S in G.
    change (slot_start_g Mb S i) with p0 in G.
    assert (Ep0 : slot_start mt i = p0) by reflexivity.
    destruct Hst as [(n & ->) | (ch & -> & ->)].
    - set (pp := p0 + 16 * soff) in G. assert (Epp : p = pp) by (subst pp; rewrite Hp, Ep0; reflexivity).
      rewrite Epp. exists (Z.min (slot_end_g Mb S i - pp - n) 5).
      split.
      { pose proof (wf_live A HW ma mt aib slots i soff n Hma Hr Hi Hi0) as (Ho & Hn & Hfit & _).
        unfold slot_end_g. subst pp p0 S. llia. }
      split; [| split].
      + destruct (soff =? 0) eqn:E.
        * apply Z.eqb_eq in E. replace (pp - 4) with (p0 - 4) by (subst pp; llia). apply G. cbn. left. reflexivity.
        * apply G. apply in_app_iff. right. apply in_app_iff. left. cbn. right. right. left. reflexivity.
      + apply G. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. left. reflexivity.
      + apply G. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. right. left. reflexivity.
    - rewrite Z.mul_0_r, Z.add_0_r in Hp. rewrite Hp, Ep0. exists 6. split; [llia|]. split; [| split].
      + apply G. cbn. left. reflexivity.
      + apply G. cbn. right. right. left. reflexivity.
      + apply G. cbn. right. right. right. left. reflexivity.
  Qed.

  Theorem get_meta_ok : forall (k : word -> M R) P,
    tsafe (k (Z_to_bv 64 ma) s) P ->
    tsafe ((x <- m_get_meta (Z_to_bv 64 p) ;; k x) s) P.
  Proof using HR HRO HW HWIN Hi Hi0 Hma Hp Hr Hst MLok p0. pu_keep (HR, HRO, HW, HWIN, Hi, Hi0, Hma, Hp, Hr, Hst, MLok, p0).
    intros k P HK.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16. fold S in HS16.
    fold S in Hfit, Hce. fold Mb in Hal16, Hmem, Hfit, Hce, Hpg.
    destruct (stride_16 mt) as [q Hq]. fold S in Hq.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (Hi32 : i <= mt_last mt /\ i < 32) by (unfold mt_cnt, mt_last in Hic |- *; pose proof (w_last_range (mt_w32 mt)); llia).
    pose proof (grp_heap A ma mt aib slots HW Hma Hr) as (G1 & G2 & G3). unfold gext_lo, gext_hi in G1, G2, G3. fold Mb S in G1, G2, G3.
    ceil.
    assert (HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S) by (subst S; lnia).
    (* [comment removed for export] *)
    assert (Hsoff : 0 <= soff /\ 16 * soff <= S - 4 /\ soff <= 255).
    { destruct Hst as [(n & E) | (ch & E & ->)]; [| llia].
      subst st. pose proof (wf_live A HW ma mt aib slots i soff n Hma Hr Hi Hi0) as (Ho & Hn & Hf & _ & H255). fold S in Hf. llia. }
    assert (Ep : p = p0 + 16 * soff) by (rewrite Hp; reflexivity).
    set (off16 := (p - Mb - 16) / 16).
    assert (Eoff16 : 16 * off16 = p - Mb - 16).
    { subst off16. rewrite Ep. unfold p0. rewrite Hq.
      replace (Mb + 16 + i * (16 * q) + 16 * soff - Mb - 16) with ((i * q + soff) * 16) by llia.
      rewrite Z.div_mul by llia. llia. }
    assert (Hoff16 : 0 <= off16 < 2^16).
    { destruct (Z.eq_dec (mt_last mt) 0) as [Hl0 | Hl0].
      - assert (i = 0) by llia. subst off16. rewrite Ep. unfold p0. rewrite H. llia.
      - pose proof (wf_span A HW ma mt aib slots Hma Hr ltac:(pose proof (w_last_range (mt_w32 mt)); unfold mt_last in *; llia)) as Hsp.
        fold S in Hsp. rewrite Ep in Eoff16. unfold p0 in Eoff16. lnia. }
    destruct slot_hdr_facts as (c & Hc & F4 & F3 & F2). fold off16 in F2.
    unfold m_get_meta.
    assert (Hp64 : 16 <= p /\ p + S - 16 * soff <= 2^64 - 2^40) by (rewrite Ep; unfold p0; llia).
    assert (Hpal : p mod 16 = 0).
    { rewrite Ep. unfold p0. rewrite Hq.
      replace (Mb + 16 + i * (16 * q) + 16 * soff) with ((1 + i * q + soff) * 16 + Mb) by llia.
      rewrite Z.add_mod, Z.mod_mul, Z.add_0_l, Z.mod_mod, Hal16 by llia. reflexivity. }
    (* [comment removed for export] *)
    reassoc. rewrite v_andi_Z by llia. change 15 with (2^4 - 1). rewrite land_ones_low by llia. change (2^4) with 16.
    rewrite Hpal. apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    reassoc; rewrite at_Z. replace (p + -4) with (p - 4) by llia.
    eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact F4 | llia |].
    reassoc; rewrite at_Z. replace (p + -3) with (p - 3) by llia.
    eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact F3 | llia |].
    reassoc; rewrite at_Z. replace (p + -2) with (p - 2) by llia.
    eapply (ts_lhu_fact A HW); [exact HR | exact HWIN | exact F2 | llia |].
    reassoc. change (is0 (Z_to_bv 64 0)) with true. cbn iota. apply ts_bind_ret.
    (* [comment removed for export] *)
    reassoc. rewrite v_slli_Z by llia. change (2^4) with 16. rewrite v_sub_Z, at_Z.
    replace (p - off16 * 16 + -16) with Mb by llia.
    (* [comment removed for export] *)
    destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & kk & Hpga & Hkk & Ema).
    destruct (wf_areas_al A HW pg Hpga) as [Hpgal Hpgh]. unfold heap_range in Hpgh. ceil.
    assert (Hma64 : 0 <= ma /\ ma + 40 <= 2^64 - 2^40) by (rewrite Ema; unfold meta_addr; llia).
    eapply (ts_ld_fact A HW _ Mb ma); [exact HR | exact HWIN | | llia |].
    { right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. left. cbn. left. reflexivity. }
    reassoc; rewrite at_Z. change (ma + 16) with (ma + moff FMem).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FMem) with Mb; llia |].
    change (mt_f mt FMem) with Mb.
    reassoc. apply ts_assert; [apply c_eq_refl|].
    (* [comment removed for export] *)
    reassoc; rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | exact Hw32 |].
    change (mt_f mt FW32) with (mt_w32 mt).
    destruct (w32_fields (mt_w32 mt) ltac:(llia)) as (EWlast & EWsc & EWml).
    assert (Eidx : Z.land (i + 32 * c) 31 = i) by (rewrite land_31 by llia; rewrite Z.mul_comm, Z.mod_add by llia; apply Z.mod_small; llia).
    rewrite !v_andi_Z by llia. rewrite EWlast, Eidx.
    reassoc. apply ts_assert.
    { unfold mt_last in Hi32. pose proof (w_last_range (mt_w32 mt)). rewrite c_ltu_Z by llia.
      replace (w_last (mt_w32 mt) <? i) with false by (symmetry; apply Z.ltb_ge; llia). reflexivity. }
    (* [comment removed for export] *)
    assert (Hbits : Z.testbit (mt_avail mt) i = false /\ Z.testbit (mt_freed mt) i = false).
    { pose proof (Hidle i st Hi Hi0) as Hid. rewrite Z.lor_spec in Hid.
      destruct (Z.testbit (mt_avail mt) i), (Z.testbit (mt_freed mt) i); try (split; reflexivity);
        exfalso; (assert (X : st = SIdle) by (apply Hid; reflexivity));
        destruct Hst as [(n & E) | (ch & E & _)]; rewrite X in E; discriminate. }
    destruct Hbits as [Hba Hbf].
    rewrite v_sllw_1 by llia.
    reassoc; rewrite at_Z. change (ma + 24) with (ma + moff FAvail).
    eapply (ts_lw_meta32 A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FAvail) with (mt_avail mt); unfold mt_cnt, mt_last in Hav; pose proof (w_last_range (mt_w32 mt)); split; [llia|]; apply Z.lt_le_trans with (2 ^ (w_last (mt_w32 mt) + 1)); [llia | apply Z.pow_le_mono_r; llia] |].
    change (mt_f mt FAvail) with (mt_avail mt).
    reassoc. apply ts_assert.
    { rewrite mask_bit_test; [rewrite Hba; reflexivity | | llia].
      unfold mt_cnt, mt_last in Hav. pose proof (w_last_range (mt_w32 mt)). split; [llia|].
      apply Z.lt_le_trans with (2 ^ (w_last (mt_w32 mt) + 1)); [llia | apply Z.pow_le_mono_r; llia]. }
    reassoc; rewrite at_Z. change (ma + 28) with (ma + moff FFreed).
    eapply (ts_lw_meta32 A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FFreed) with (mt_freed mt); unfold mt_cnt, mt_last in Hfd; pose proof (w_last_range (mt_w32 mt)); split; [llia|]; apply Z.lt_le_trans with (2 ^ (w_last (mt_w32 mt) + 1)); [llia | apply Z.pow_le_mono_r; llia] |].
    change (mt_f mt FFreed) with (mt_freed mt).
    reassoc. apply ts_assert.
    { rewrite mask_bit_test; [rewrite Hbf; reflexivity | | llia].
      unfold mt_cnt, mt_last in Hfd. pose proof (w_last_range (mt_w32 mt)). split; [llia|].
      apply Z.lt_le_trans with (2 ^ (w_last (mt_w32 mt) + 1)); [llia | apply Z.pow_le_mono_r; llia]. }
    (* [comment removed for export] *)
    assert (Epg : Z.land ma (2^64 - 4096) = pg).
    { rewrite land_pagemask by llia. rewrite Ema. unfold meta_addr. unfold page_aligned in Hpgal.
      replace (pg + 24 + 40 * kk) with ((24 + 40 * kk) + (pg / 4096) * 4096) by (pose proof (Z.div_mod pg 4096 ltac:(llia)); llia).
      rewrite Z.div_add by llia. rewrite Z.div_small by llia. pose proof (Z.div_mod pg 4096 ltac:(llia)). llia. }
    pose proof (wf_ctx_nonneg A HW KSecret) as Hsec0.
    reassoc; rewrite PAGEMASK_eq, v_and_Z by llia. rewrite Epg.
    eapply (ts_ld_fact A HW _ pg (a_ctx A KSecret)); [exact HR | exact HWIN | | exact Hsec0 |].
    { right; left. exists pg. split; [exact Hpga | reflexivity]. }
    reassoc. rewrite A_CTX_eq.
    eapply (ts_ld_ctx_nn A); [exact HR | exact HWIN | exact I | reflexivity | exact Hsec0 |].
    reassoc. apply ts_assert; [apply c_eq_refl|].
    (* [comment removed for export] *)
    rewrite v_slli_Z by llia. rewrite <- (ZZ_mod (mt_w32 mt * 2^52)).
    rewrite v_srli_Z by (pose proof (Z.mod_pos_bound (mt_w32 mt * 2^52) (2^64)); llia). rewrite EWsc.
    change (w_sc (mt_w32 mt)) with (mt_sc mt). pose proof (w_sc_range (mt_w32 mt)) as Hscr. change (w_sc (mt_w32 mt)) with (mt_sc mt) in Hscr.
    unfold wlit at 1. rewrite c_ltu_Z by llia.
    reassoc.
    apply (ts_bind_split _ _ s P (fun (_ : unit) s' => s' = s)).
    { destruct Hsc as [Hsc48 | (Hsc63 & Hl0 & Hml)].
      - replace (47 <? mt_sc mt) with false by (symmetry; apply Z.ltb_ge; llia).
        rewrite v_slli_Z by llia. rewrite A_SIZE_CLASSES_eq. rewrite v_add_Z.
        replace (T_SIZE_CLASSES + mt_sc mt * 2^1) with (T_SIZE_CLASSES + 2 * mt_sc mt) by llia.
        eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
        pose proof (size_class_bound (mt_sc mt) ltac:(llia)) as Hszc.
        rewrite v_mul_Z, v_addi_Z, v_mul_Z.
        (* [comment removed for export] *)
        assert (Hgeom : size_class (mt_sc mt) * i <= off16 < (i + 1) * size_class (mt_sc mt)).
        { assert (E16 : off16 = i * q + soff) by lnia.
          unfold S, mt_stride in Hq.
          destruct ((mt_maplen mt =? 0) || negb (mt_last mt =? 0)) eqn:Eb.
          - assert (q = size_class (mt_sc mt)) by llia. subst q. rewrite E16.
            unfold S, mt_stride in Hsoff. rewrite Eb in Hsoff. (clear -Hsoff; replace (size_class (mt_sc mt) * i) with (i * size_class (mt_sc mt)) by ring;
             replace ((i + 1) * size_class (mt_sc mt)) with (i * size_class (mt_sc mt) + size_class (mt_sc mt)) by ring; lia).
          - apply Bool.orb_false_iff in Eb. destruct Eb as [E1 E2]. apply Bool.negb_false_iff in E2.
            apply Z.eqb_neq in E1. apply Z.eqb_eq in E2.
            assert (i = 0) by llia. subst i.
            assert (Hml0 : 0 < mt_maplen mt) by (unfold mt_maplen, w_maplen in *; pose proof (Z.div_pos (mt_w32 mt) 4096); llia).
            pose proof (wf_single A HW ma mt aib slots Hma Hr E2 Hml0 Hsc48) as [H256 | H256]; [lnia|].
            unfold S in Hsoff. lnia. }
        apply ts_assert.
        assert (HPr : 0 <= size_class (mt_sc mt) * i <= 8191 * 31 /\ 0 <= (i + 1) * size_class (mt_sc mt) <= 32 * 8191)
          by (clear -Hszc Hi32 Hi0; nia).
        { rewrite c_ltu_Z by lia. replace (off16 <? size_class (mt_sc mt) * i) with false by (symmetry; apply Z.ltb_ge; llia). reflexivity. }
        rewrite c_ltu_Z by lia. replace (off16 <? (i + 1) * size_class (mt_sc mt)) with true by (symmetry; apply Z.ltb_lt; llia).
        exact eq_refl.
      - rewrite Hsc63. cbn. reflexivity. }
    intros [] s' ->.
    (* [comment removed for export] *)
    rewrite v_srli_Z by llia. rewrite EWml. change (w_maplen (mt_w32 mt)) with (mt_maplen mt).
    assert (Hmlr : 0 <= mt_maplen mt < 2^52) by (unfold mt_maplen, w_maplen; split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
    rewrite is0_Z by llia.
    reassoc.
    apply (ts_bind_split _ _ s P (fun (_ : unit) s' => s' = s)).
    { destruct (mt_maplen mt =? 0) eqn:Eml; [reflexivity|]. apply Z.eqb_neq in Eml.
      rewrite v_slli_Z, v_addi_Z by llia. change (2^8) with 256.
      rewrite c_ltu_Z by llia.
      replace (mt_maplen mt * 256 + -1 <? off16) with false; [exact eq_refl|]. symmetry. apply Z.ltb_ge.
      assert (Hfit' : 16 + mt_cnt mt * S <= grp_map_len mt).
      { replace (mt_maplen mt =? 0) with false in Hfit by (symmetry; apply Z.eqb_neq; llia). exact Hfit. }
      unfold grp_map_len in Hfit'. rewrite Ep in Eoff16. unfold p0 in Eoff16. clear -Hfit' Eoff16 HiS Hsoff; lia. }
    intros [] s' ->.
    apply ts_bind_ret. exact HK.
  Qed.
End GetMeta.

End WithLayout.
