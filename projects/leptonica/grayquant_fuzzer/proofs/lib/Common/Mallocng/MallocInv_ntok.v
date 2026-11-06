(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_ops MallocInv_getmeta MallocInv_free MallocInv_tryavail
  MallocInv_ntpieces MallocInv_ntq.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Lemma grp_next_range : forall A ma mt aib slots, WF A -> a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  0 <= mt_next mt < 2^64 /\ 0 <= mt_prev mt < 2^64 /\
  (mt_next mt <> 0 -> In ma (a_active A (mt_sc mt)) /\ mt_sc mt < 48).
Proof.
  intros A ma mt aib slots HW Hma Hr.
  destruct (wf_grp A HW ma mt aib slots Hma Hr) as (_ & _ & Hsc & _). pose proof (w_sc_range (mt_w32 mt)) as Hscr.
  destruct Hsc as [Hsc48 | (H63 & _)].
  2:{ pose proof (wf_act63 A HW ma mt aib slots Hma Hr H63) as [Hp Hn]. rewrite Hp, Hn.
      split; [llia|]. split; [llia|]. intros H. exfalso. exact (H eq_refl). }
  destruct (in_dec Z.eq_dec ma (a_active A (mt_sc mt))) as [Hin | Hnin].
  - destruct (In_nth_error _ _ Hin) as [k Hk].
    destruct (wf_act_dll A HW (mt_sc mt) ltac:(unfold mt_sc in *; llia) k ma Hk) as (mt' & Hm' & Hn & Hp). rewrite Hma in Hm'. injection Hm' as <-.
    assert (Hlen : (0 < length (a_active A (mt_sc mt)))%nat) by (destruct (a_active A (mt_sc mt)); [destruct Hin | cbn; lia]).
    assert (RG : forall j, (j < length (a_active A (mt_sc mt)))%nat -> 0 <= nth j (a_active A (mt_sc mt)) 0 < 2^64).
    { intros j Hj. destruct (wf_act_mem A HW (mt_sc mt) _ (nth_In _ 0 Hj)) as (mtj & aibj & slj & Hmj & _). ceil.
      pose proof (meta_facts A _ mtj HW Hmj) as (X1 & X2 & _). llia. }
    rewrite Hn, Hp. split; [apply RG; apply Nat.mod_upper_bound; lia|]. split; [apply RG; apply Nat.mod_upper_bound; lia|].
    intros _. auto.
  - pose proof (wf_unlinked A HW ma mt aib slots Hma Hr Hnin) as [Hp Hn]. rewrite Hp, Hn.
    split; [llia|]. split; [llia|]. intros H. exfalso. exact (H eq_refl).
Qed.

Section OkComp.
  Context {R : Type}.
  Variables (A : astate) (s : mstate).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  Implicit Types (P : R -> mstate -> Prop).

  Let mask := Z.lor (mt_avail mt) (mt_freed mt).
  Let sc := mt_sc mt.

  Theorem ts_nt_okcomp : forall (K : bool -> M R) P,
    (forall ok : bool,
       (ok = true -> mask + 2 ^ i = 2 ^ mt_cnt mt - 1) ->
       (ok = false -> mask = 0 -> sc < 48 /\ 16 * size_class sc <= mt_stride mt) ->
       tsafe (K ok s) P) ->
    tsafe ((ok <- nt_okcomp (Z_to_bv 64 ma) (Z_to_bv 64 (mt_w32 mt)) (w32 mask) (w32 (2 ^ i)) (Z_to_bv 64 sc) ;; K ok) s) P.
  Proof.
    intros K P HK.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfree & Hsc & Hlen & Hav & Hfr & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (w_last_range (mt_w32 mt)) as Hlr. pose proof (w_sc_range (mt_w32 mt)) as Hscr.
    change (w_last (mt_w32 mt)) with (mt_last mt) in Hlr. change (w_sc (mt_w32 mt)) with sc in Hscr.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia. assert (Hcl : mt_cnt mt = mt_last mt + 1) by reflexivity.
    assert (Hcnt32 : 2 ^ mt_cnt mt <= 2 ^ 32) by (apply Z.pow_le_mono_r; llia).
    pose proof (lor_range32 (mt_avail mt) (mt_freed mt) ltac:(llia) ltac:(llia)) as Hm32. change (Z.lor (mt_avail mt) (mt_freed mt)) with mask in Hm32.
    assert (Hbit : Z.testbit mask i = false).
    { destruct (Z.testbit mask i) eqn:E; [| reflexivity]. exfalso. pose proof (proj1 (Hidle i STaken Hi Hi0) E). discriminate. }
    destruct (add_clear_bit mask i (mt_cnt mt)) as [_ Hsum];
      [subst mask; apply (lor_range (mt_avail mt) (mt_freed mt) (mt_cnt mt)); llia | llia | exact Hbit |].
    pose proof (maplen_nonneg mt ltac:(llia)) as Hml0.
    assert (Hml64 : mt_maplen mt < 2^52) by (unfold mt_maplen, w_maplen; apply Z.div_lt_upper_bound; llia).
    ceil. pose proof (meta_facts A ma mt HW Hma) as (M1 & M2 & _).
    unfold nt_okcomp.
    (* [comment removed for export] *)
    rewrite v_andi_Z by llia.
    assert (Hfb : Z.land (mt_w32 mt) 32 <> 0).
    { intros E. pose proof (Z.land_spec (mt_w32 mt) 32 5) as B. rewrite E, Z.bits_0 in B.
      change (Z.testbit 32 5) with true in B. rewrite Bool.andb_true_r in B.
      symmetry in B. apply Z.testbit_false in B; [| lia]. unfold w_freeable in Hfree. change (2^5) with 32 in B. llia. }
    rewrite is0_Z by (pose proof (Z.land_nonneg (mt_w32 mt) 32); pose proof (land_le_left (mt_w32 mt) 32); llia).
    replace (Z.land (mt_w32 mt) 32 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfb).
    (* [comment removed for export] *)
    rewrite v_addw_w32, (wall_eq mt) by llia. rewrite c_eq_w32.
    rewrite !Z.mod_small by (unfold mt_cnt in *; llia).
    destruct (Z.eqb_spec (mask + 2 ^ i) (2 ^ mt_cnt mt - 1)) as [Eall | Nall]; cbn [negb].
    2:{ (* [comment removed for export] *)
        apply HK; [discriminate|]. intros _ Hm0.
        assert (Hl1 : mt_last mt <> 0).
        { intros El. apply Nall. rewrite Hm0. unfold mt_cnt. rewrite El. replace i with 0 by llia. reflexivity. }
        split; [llia|]. unfold mt_stride. replace (negb (mt_last mt =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hl1).
        rewrite Bool.orb_true_r. cbn [orb]. subst sc. llia. }
    (* [comment removed for export] *)
    unfold wlit at 1. rewrite c_ltu_Z by llia.
    destruct (Z.ltb_spec 47 sc) as [Hbig | Hsmall]; [apply HK; [auto | intros E; discriminate E] |].
    cbv zeta. rewrite (wlast_eq mt), (wmaplen_eq mt) by llia.
    rewrite !is0_Z by llia.
    (* [comment removed for export] *)
    reassoc.
    rewrite v_slli_Z, A_SIZE_CLASSES_eq by llia.
    rewrite v_srli_Z, v_andi_Z by (try split; try apply Z.div_pos; try apply Z.div_lt_upper_bound; llia).
    change (2^5) with 32. rewrite (sc_index (mt_w32 mt)) by llia. change ((mt_w32 mt / 64) mod 64) with sc.
    rewrite !v_add_Z. replace (T_SIZE_CLASSES + sc * 2 ^ 1) with (T_SIZE_CLASSES + 2 * sc) by lia.
    apply (ts_bind_split _ _ s P (fun (b : bool) s' => s' = s /\ (b = false -> 16 * size_class sc <= mt_stride mt /\ mt_maplen mt <> 0))).
    { destruct (Z.eqb_spec (mt_maplen mt) 0) as [Hml | Hml]; destruct (Z.eqb_spec (mt_last mt) 0) as [Hl0 | Hl0]; cbn [negb andb].
      - eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |]. cbn [tsafe mret]. split; [reflexivity | intros E; discriminate E].
      - eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |]. cbn [tsafe mret]. split; [reflexivity | intros E; discriminate E].
      - (* [comment removed for export] *)
        eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
        pose proof (size_class_bound sc ltac:(llia)) as Hszc.
        rewrite PAGEMASK_eq, v_and_Z, land_pagemask by llia. change (mt_w32 mt / 4096) with (mt_maplen mt).
        rewrite v_addi_Z, v_slli_Z, c_ltu_Z by llia.
        cbn [tsafe mret]. split; [reflexivity|]. intros Hlt. apply (proj1 (Z.ltb_ge _ _)) in Hlt. change (2^4) with 16 in Hlt. split; [| exact Hml].
        unfold mt_stride. rewrite (proj2 (Z.eqb_neq _ _) Hml), Hl0. cbn [Z.eqb negb orb]. llia.
      - eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
        eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
        pose proof (size_class_bound sc ltac:(llia)) as Hszc.
        rewrite !v_slli_Z, c_ltu_Z by llia. rewrite Z.ltb_irrefl.
        cbn [tsafe mret]. split; [reflexivity|]. intros _. split; [| exact Hml].
        unfold mt_stride. replace (negb (mt_last mt =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Hl0).
        rewrite Bool.orb_true_r. cbn [orb]. subst sc. llia. }
    intros b s1 [-> Hb].
    destruct b; [apply HK; [auto | intros E; discriminate E] |].
    destruct (Hb eq_refl) as [Hstr Hml].
    replace (mt_maplen mt =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml).
    (* [comment removed for export] *)
    pose proof (grp_next_range A ma mt aib slots HW Hma Hr) as (Hnr & Hpr & _).
    reassoc. rewrite at_Z. change (ma + 8) with (ma + moff FNext).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FNext) with (mt_next mt); llia |].
    change (mt_f mt FNext) with (mt_next mt). rewrite c_eq_Z by llia.
    destruct (Z.eqb_spec (mt_next mt) ma) as [Hnx | Hnx]; cbn [negb]; [| apply HK; [auto | intros E; discriminate E]].
    (* [comment removed for export] *)
    rewrite v_addi_Z. unfold wlit at 1.
    destruct (Z.lt_ge_cases sc 7) as [Hlt7 | Hge7].
    { rewrite <- (ZZ_mod (sc + -7)). rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (sc + -7) (2^64)); llia).
      replace (31 <? (sc + -7) mod 2 ^ 64) with true; [apply HK; [auto | intros E; discriminate E] |].
      symmetry. apply Z.ltb_lt. replace (sc + -7) with (-(7 - sc)) by lia. rewrite Z.mod_opp_l_nz by llia. rewrite Z.mod_small by llia. llia. }
    rewrite c_ltu_Z by llia.
    destruct (Z.ltb_spec 31 (sc + -7)) as [Hgt38 | Hle38]; [apply HK; [auto | intros E; discriminate E] |].
    rewrite addr_bounce. reassoc.
    eapply (ts_lbu_ctx_m A HW); [exact HR | exact HWIN | cbn; llia | reflexivity |].
    unfold wlit at 1. rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (a_ctx A (KBounce (sc + -7))) 256); llia).
    destruct (a_ctx A (KBounce (sc + -7)) mod 256 <? 100); [apply HK; [auto | intros E; discriminate E] |].
    rewrite (addr_usage sc) by llia. reassoc.
    eapply (ts_ld_ctx_m A HW); [exact HR | exact HWIN | cbn; llia | reflexivity |].
    rewrite v_slli_Z, v_add_Z, v_addi_Z by llia.
    rewrite c_ltu_Z by (pose proof (Z.mod_pos_bound (a_ctx A (KUsage sc)) (2^64)); llia).
    destruct (a_ctx A (KUsage sc) mod 2 ^ 64 <? mt_last mt * 2 ^ 3 + mt_last mt + 9).
    { apply HK; [intros E; discriminate E|]. intros _ _. split; [llia | exact Hstr]. }
    unfold wlit. rewrite c_ltu_Z by llia.
    destruct (18 <? mt_last mt); apply HK; try (intros E; discriminate E); auto.
    intros _ _. split; [llia | exact Hstr].
  Qed.
End OkComp.

End WithLayout.
