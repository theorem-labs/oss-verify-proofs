(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocCallocFacts MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_tables MallocInv_steps MallocInv_w32 MallocInv_live
  MallocInv_env MallocInv_ops MallocInv_getmeta MallocInv_coh MallocIface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_3072 : forall n, 0 <= n -> Z.testbit 3072 n = ((n =? 10) || (n =? 11))%bool.
Proof.
  intros n Hn. change 3072 with (Z.lor (2 ^ 10) (2 ^ 11)). rewrite Z.lor_spec, !Z.pow2_bits_eqb by lia.
  rewrite (Z.eqb_sym 10 n), (Z.eqb_sym 11 n). reflexivity.
Qed.

Lemma land_3072 : forall w, 0 <= w ->
  Z.land w 3072 = 3072 <-> (Z.testbit w 10 = true /\ Z.testbit w 11 = true).
Proof.
  intros w Hw. split.
  - intros E. split.
    + pose proof (f_equal (fun z => Z.testbit z 10) E) as X. cbn beta in X. rewrite Z.land_spec, testbit_3072 in X by lia.
      cbn in X. rewrite andb_true_r in X. exact X.
    + pose proof (f_equal (fun z => Z.testbit z 11) E) as X. cbn beta in X. rewrite Z.land_spec, testbit_3072 in X by lia.
      cbn in X. rewrite andb_true_r in X. exact X.
  - intros [H10 H11]. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_3072 by lia.
    destruct (Z.eqb_spec n 10) as [-> | N10]; [rewrite H10; reflexivity|].
    destruct (Z.eqb_spec n 11) as [-> | N11]; [rewrite H11; reflexivity|].
    cbn. apply andb_false_r.
Qed.

Lemma land_3072_range : forall w, 0 <= w -> 0 <= Z.land w 3072 < 4096.
Proof.
  intros w Hw. assert (H0 : 0 <= Z.land w 3072) by (apply Z.land_nonneg; lia). split; [exact H0|].
  destruct (Z.eq_dec (Z.land w 3072) 0) as [-> | Hne]; [lia|].
  change 4096 with (2 ^ 12). apply (proj2 (Z.log2_lt_pow2 (Z.land w 3072) 12 ltac:(lia))).
  pose proof (Z.log2_land w 3072 Hw ltac:(lia)) as X. assert (E : Z.log2 3072 = 11) by reflexivity. rewrite E in X. lia.
Qed.

Lemma sc48_iff : forall w, 0 <= w -> (Z.land w 3072 = 3072 <-> 48 <= w_sc w).
Proof.
  intros w Hw. rewrite (land_3072 w Hw). rewrite !Z.testbit_true by lia.
  change (2 ^ 10) with 1024. change (2 ^ 11) with 2048. unfold w_sc. split; intros H; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllZero.
  Context {R : Type}.
  Variables (A : astate) (s : mstate).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z) (off n p : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some (SLive off n).
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hp : p = slot_start mt i + 16 * off.
  Implicit Types (P : R -> mstate -> Prop).

  Theorem allzerop_ok : forall (k : word -> M R) P,
    (forall z : word, (u z <> 0 -> zslot mt) -> tsafe (k z s) P) ->
    tsafe ((z <- m_allzerop (Z_to_bv 64 p) ;; k z) s) P.
  Proof.
    intros k P HK.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    destruct (w32_fields (mt_w32 mt) ltac:(llia)) as (EWlast & EWsc & EWml).
    pose proof (w_sc_range (mt_w32 mt)) as Hscr. change (w_sc (mt_w32 mt)) with (mt_sc mt) in Hscr.
    pose proof (w_last_range (mt_w32 mt)) as Hlr.
    unfold m_allzerop. reassoc.
    apply (get_meta_ok A s HW HR HWIN HRO ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp).
    cbv beta zeta.
    reassoc; rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | exact Hw32 |].
    change (mt_f mt FW32) with (mt_w32 mt).
    (* [comment removed for export] *)
    unfold wlit. rewrite v_and_Z by llia. pose proof (land_3072_range (mt_w32 mt) ltac:(lia)) as Hl3. rewrite c_eq_Z by lia.
    destruct (Z.eqb_spec (Z.land (mt_w32 mt) 3072) 3072) as [E3 | N3].
    - apply ts_bind_ret. apply HK. intros _. left. apply (proj1 (sc48_iff (mt_w32 mt) ltac:(lia))). exact E3.
    - assert (Hsc48 : mt_sc mt < 48).
      { destruct (Z.lt_ge_cases (mt_sc mt) 48) as [L|L]; [exact L|]. exfalso. apply N3. apply (proj2 (sc48_iff (mt_w32 mt) ltac:(lia))). exact L. }
      (* [comment removed for export] *)
      rewrite v_srli_Z by llia. change (2 ^ 12) with 4096. rewrite v_andi_Z by llia. rewrite EWlast.
      change (w_last (mt_w32 mt)) with (mt_last mt). change (w_last (mt_w32 mt)) with (mt_last mt) in Hlr.
      replace (mt_w32 mt / 4096) with (mt_maplen mt) by reflexivity.
      pose proof (Z.div_pos (mt_w32 mt) 4096 ltac:(lia) ltac:(lia)) as Hml0. change (mt_w32 mt / 4096) with (mt_maplen mt) in Hml0.
      assert (Hmlhi : mt_maplen mt < 2^52) by (unfold mt_maplen, w_maplen; apply Z.div_lt_upper_bound; lia).
      rewrite !is0_Z by lia.
      (* [comment removed for export] *)
      rewrite v_slli_Z by llia. rewrite <- (ZZ_mod (mt_w32 mt * 2^52)).
      rewrite v_srli_Z by (pose proof (Z.mod_pos_bound (mt_w32 mt * 2^52) (2^64)); llia). rewrite EWsc.
      change (w_sc (mt_w32 mt)) with (mt_sc mt).
      rewrite v_slli_Z by llia. change (2 ^ 1) with 2. rewrite A_SIZE_CLASSES_eq, v_add_Z.
      replace (T_SIZE_CLASSES + mt_sc mt * 2) with (T_SIZE_CLASSES + 2 * mt_sc mt) by lia.
      pose proof (size_class_bound (mt_sc mt) ltac:(lia)) as Hszb.
      destruct ((negb (mt_maplen mt =? 0) && (mt_last mt =? 0))%bool) eqn:Eb.
      + apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply negb_true_iff in E1. apply Z.eqb_neq in E1. apply Z.eqb_eq in E2.
        reassoc. eapply (ts_lhu_size_class); [exact HRO | exact HWIN | lia |].
        apply ts_bind_ret. apply HK. intros Hz. right.
        rewrite PAGEMASK_eq, v_and_Z, land_pagemask in Hz by llia. rewrite v_addi_Z in Hz.
        rewrite !v_slli_Z in Hz by llia. change (2 ^ 4) with 16 in Hz.
        change (mt_w32 mt / 4096) with (mt_maplen mt) in Hz.
        rewrite v_sltu_Z in Hz by lia.
        destruct (Z.ltb_spec (4096 * mt_maplen mt + -16) (size_class (mt_sc mt) * 16)) as [L | L]; [| rewrite uZ in Hz by lia; exfalso; exact (Hz eq_refl)].
        unfold mt_stride. rewrite (proj2 (Z.eqb_neq _ _) E1), E2. cbn [Z.eqb orb negb]. lia.
      + reassoc. eapply (ts_lhu_size_class); [exact HRO | exact HWIN | lia |].
        apply ts_bind_ret. apply HK. intros Hz. exfalso. apply Hz.
        rewrite !v_slli_Z by llia. rewrite v_sltu_Z by lia. rewrite Z.ltb_irrefl. reflexivity.
  Qed.
End AllZero.

(* [comment removed for export] *)
Corollary allzerop_AZ : forall A s ma mt aib slots i off n p (sz : Z),
  WF A -> Rep A (ms_mem s) -> WIN s -> rodata_clear (ms_mem s) ->
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> nth_error slots (Z.to_nat i) = Some (SLive off n) -> 0 <= i ->
  p = slot_start mt i + 16 * off ->
  (zslot mt -> zero_at (ms_mem s) p (p + sz)) ->
  exists AZ : word -> mstate -> Prop,
    tsafe (m_allzerop (Z_to_bv 64 p) s) AZ /\
    (forall z s'', AZ z s'' -> s'' = s /\ (u z <> 0 -> zero_at (ms_mem s) p (p + sz))).
Proof.
  intros A s ma mt aib slots i off n p sz HW HR HWIN HRO Hma Hr Hi Hi0 Hp Hz.
  exists (fun z s'' => s'' = s /\ (u z <> 0 -> zero_at (ms_mem s) p (p + sz))). split; [| intros z s'' H; exact H].
  apply (tsafe_leaves_of_cps (m_allzerop (Z_to_bv 64 p)) s). intros K' P' HK'.
  apply (allzerop_ok A s HW HR HWIN HRO ma mt aib slots i off n p Hma Hr Hi Hi0 Hp). intros z Hzs. apply HK'.
  split; [reflexivity|]. intros Hnz. apply Hz. exact (Hzs Hnz).
Qed.

(* [comment removed for export] *)
Corollary allzerop_live : forall {R : Type} A s p n (k : word -> M R) (P : R -> mstate -> Prop),
  WF A -> Rep A (ms_mem s) -> WIN s -> rodata_clear (ms_mem s) -> a_live A p = Some n ->
  (forall z : word, (u z <> 0 -> zgroup A p) -> tsafe (k z s) P) ->
  tsafe ((z <- m_allzerop (Z_to_bv 64 p) ;; k z) s) P.
Proof.
  intros R A s p n k P HW HR HWIN HRO Hl HK.
  destruct (proj1 (wf_live_map A HW p n) Hl) as (ma & mt & aib & slots & i & off & Hma & Hr & Hi0 & Hi & Hp).
  apply (allzerop_ok A s HW HR HWIN HRO ma mt aib slots i off n p Hma Hr Hi Hi0 Hp).
  intros z Hz. apply HK. intros Hnz. exists ma, mt, aib, slots, i, off, n. split; [exact Hma|]. split; [exact Hr|].
  split; [exact Hi0|]. split; [exact Hi|]. split; [exact Hp | exact (Hz Hnz)].
Qed.

Corollary allzerop_live_AZ : forall A s p n (sz : Z),
  WF A -> Rep A (ms_mem s) -> WIN s -> rodata_clear (ms_mem s) -> a_live A p = Some n ->
  (zgroup A p -> zero_at (ms_mem s) p (p + sz)) ->
  exists AZ : word -> mstate -> Prop,
    tsafe (m_allzerop (Z_to_bv 64 p) s) AZ /\
    (forall z s'', AZ z s'' -> s'' = s /\ (u z <> 0 -> zero_at (ms_mem s) p (p + sz))).
Proof.
  intros A s p n sz HW HR HWIN HRO Hl Hz.
  exists (fun z s'' => s'' = s /\ (u z <> 0 -> zero_at (ms_mem s) p (p + sz))). split; [| intros z s'' H; exact H].
  apply (tsafe_leaves_of_cps (m_allzerop (Z_to_bv 64 p)) s). intros K' P' HK'.
  apply (allzerop_live A s p n K' P' HW HR HWIN HRO Hl). intros z Hzs. apply HK'.
  split; [reflexivity|]. intros Hnz. apply Hz. exact (Hzs Hnz).
Qed.

End WithLayout.
