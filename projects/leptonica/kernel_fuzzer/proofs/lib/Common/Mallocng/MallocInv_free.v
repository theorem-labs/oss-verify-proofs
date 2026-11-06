(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_tables MallocInv_steps MallocInv_live MallocInv_repw MallocInv_getmeta MallocInv_coh MallocInv_env MallocInv_ops MallocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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

Lemma byte_of_testbit : forall v k j, 0 <= k -> 0 <= j ->
  Z.testbit (byte_of v k) j = if j <? 8 then Z.testbit v (8 * k + j) else false.
Proof using Type. pu_keep tt.
  intros v k j Hk Hj. unfold byte_of. change 256 with (2^8).
  destruct (j <? 8) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - rewrite Z.mod_pow2_bits_low by llia. rewrite Z.div_pow2_bits by llia. f_equal. llia.
  - rewrite Z.mod_pow2_bits_high by llia. reflexivity.
Qed.

Lemma byte_of_low32 : forall v k, 0 <= k < 4 -> byte_of (v mod 2^32) k = byte_of v k.
Proof using Type. pu_keep tt.
  intros v k Hk. apply Z.bits_inj'. intros j Hj. rewrite !byte_of_testbit by llia.
  destruct (j <? 8) eqn:E; [apply Z.ltb_lt in E | reflexivity].
  apply Z.mod_pow2_bits_low. llia.
Qed.

Lemma byte_of_mod32 : forall v w k, 0 <= k < 4 -> v mod 2^32 = w mod 2^32 -> byte_of v k = byte_of w k.
Proof using Type. pu_keep tt.
  intros v w k Hk E. rewrite <- (byte_of_low32 v k), <- (byte_of_low32 w k) by llia. rewrite E. reflexivity.
Qed.

Lemma byte_of_sx32 : forall v k, 0 <= k < 4 -> byte_of (sx32 v) k = byte_of v k.
Proof using Type. pu_keep tt. intros v k Hk. apply byte_of_mod32; [llia | apply sx32_eqmod]. Qed.

Lemma lor_range : forall a b c, 0 <= c -> 0 <= a < 2^c -> 0 <= b < 2^c -> 0 <= Z.lor a b < 2^c.
Proof using Type. pu_keep tt.
  intros a b c Hc Ha Hb. split; [apply Z.lor_nonneg; llia|].
  destruct (Z.eq_dec a 0) as [Ea|Na]. { rewrite Ea, Z.lor_0_l. llia. }
  destruct (Z.eq_dec b 0) as [Eb|Nb]. { rewrite Eb, Z.lor_0_r. llia. }
  assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; llia).
  assert (NE : Z.lor a b <> 0) by (intros E; apply Z.lor_eq_0_iff in E; llia).
  apply Z.log2_lt_pow2; [llia|]. rewrite Z.log2_lor by llia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; llia.
Qed.

Lemma add_clear_bit : forall m i c, 0 <= m < 2^c -> 0 <= i < c -> Z.testbit m i = false ->
  m + 2^i = Z.lor m (2^i) /\ m + 2^i < 2^c.
Proof using Type. pu_keep tt.
  intros m i c Hm Hi Hb.
  assert (Hd : Z.land m (2^i) = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by llia.
    destruct (Z.eq_dec i j) as [<-|NE]; [rewrite Hb; reflexivity|].
    replace (i =? j) with false by (symmetry; apply Z.eqb_neq; llia). apply andb_false_r. }
  assert (E : m + 2^i = Z.lor m (2^i)) by (rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact Hd; reflexivity).
  split; [exact E|]. rewrite E.
  assert (0 <= 2^i < 2^c) by (split; [llia | apply Z.pow_lt_mono_r; llia]).
  apply lor_range; llia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FreeLive.
  Variables (A : astate) (s : mstate).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Hypothesis HNL : rdn ml_segs (ms_mem s) A_NEED_LOCKS 1 = Some [Z_to_bv 8 0].
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i off n : Z) (p : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some (SLive off n).
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hp : p = slot_start mt i + 16 * off.

  Let S := mt_stride mt.
  Let Mb := mt_mem mt.
  Let p0 := Mb + 16 + i * S.
  Let e := p0 + S - 4.
  Let rsv := e - p - n.

  (* [comment removed for export] *)
  Let fr' := mt_freed mt + 2 ^ i.
  Let slots' := list_set slots (Z.to_nat i) SIdle.
  Let L' := lupd (a_live A) p None.
  Let A' := set_live (ameta_upd A ma (MT (gu_f mt (mt_avail mt) fr') (RGroup aib slots'))) L'.

  Let Wh3 := FCT (p - 3) 1 (2^64 - 1).
  Let Wh2 := FCT (p - 2) 2 0.
  Let Wfr := FCT (ma + 28) 4 (sx32 fr').

  (* [comment removed for export] *)
  Definition free_slow (P : unit -> mstate -> Prop) : Prop :=
    forall m2, RepW A (ms_mem s) [Wh2; Wh3] m2 ->
      (mt_freed mt = 0 \/ Z.lor (mt_avail mt) (mt_freed mt) + 2 ^ i = 2 ^ (mt_cnt mt) - 1) ->
      tsafe ((mi <- m_nontrivial_free FREE_FUEL (Z_to_bv 64 ma) (Z_to_bv 64 i) ;;
              (let '(base, len) := mi in
               m_unlock ;;
               (if is0 len then mret tt
                else e0 <- m_lw A_ERRNO ;; r <- sys_munmap base len ;; m_sw A_ERRNO e0))) (upd s m2 (ms_vm s))) P.

  Theorem free_live_ok : forall P,
    (forall m3, RepW A (ms_mem s) [Wfr; Wh2; Wh3] m3 ->
       mt_freed mt <> 0 -> Z.lor (mt_avail mt) (mt_freed mt) + 2 ^ i <> 2 ^ (mt_cnt mt) - 1 ->
       P tt (upd s m3 (ms_vm s))) ->
    free_slow P ->
    tsafe (m_free (Z_to_bv 64 p) s) P.
  Proof using HNL HR HRO HW HWIN Hi Hi0 Hma Hp Hr MLok rsv. pu_keep (HNL, HR, HRO, HW, HWIN, Hi, Hi0, Hma, Hp, Hr, MLok, rsv).
    intros P HKfast HKslow.
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
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hofit & _ & H255). fold S in Hofit.
    assert (Ep : p = p0 + 16 * off) by (rewrite Hp; reflexivity).
    unfold m_free. rewrite is0_Z by (rewrite Ep; unfold p0; llia).
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite Ep; unfold p0; llia).
    (* [comment removed for export] *)
    apply (get_meta_ok A s HW HR HWIN HRO ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp).
    (* [comment removed for export] *)
    rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | exact Hw32 |].
    change (mt_f mt FW32) with (mt_w32 mt).
    destruct (slot_hdr_facts A HW ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp) as (c & Hc & F4 & F3 & F2).
    (* [comment removed for export] *)
    assert (F3' : has A (FCT (p - 3) 1 (i + 32 * Z.min rsv 5))).
    { right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
      exists (Z.to_nat i), (SLive off n). split; [exact Hi|]. rewrite Z2Nat.id by llia.
      unfold slot_fields, slot_fields_g. fold Mb S. change (slot_start_g Mb S i) with p0.
      apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. left.
      unfold rsv, e. rewrite Ep. unfold slot_end_g, p0. reflexivity. }
    clear F3. assert (Hrsv : 0 <= rsv) by (unfold rsv, e; rewrite Ep; llia).
    set (c5 := Z.min rsv 5) in F3'. assert (Hc5 : 0 <= c5 <= 5 /\ c5 <= rsv) by (subst c5; llia).
    rewrite at_Z. replace (p + -3) with (p - 3) by llia.
    eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact F3' | llia |].
    assert (Eidx : Z.land (i + 32 * c5) 31 = i) by (rewrite land_31 by llia; rewrite Z.mul_comm, Z.mod_add by llia; apply Z.mod_small; llia).
    rewrite (v_andi_Z (i + 32 * c5) 31) by llia. rewrite !Eidx.
    (* [comment removed for export] *)
    eapply (ts_get_stride A HW); [exact HR | exact HWIN | exact HRO | exact Hma | exact Hr |]. fold S.
    rewrite at_Z. change (ma + 16) with (ma + moff FMem).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | change (mt_f mt FMem) with Mb; llia |].
    change (mt_f mt FMem) with Mb.
    rewrite !v_mul_Z, !v_add_Z, !v_addi_Z.
    replace (Mb + S + S * i + 12) with e by (unfold e, p0; llia).
    replace (Mb + S + S * i + 8) with (e - 4) by (unfold e, p0; llia).
    replace (Mb + S + S * i + 7) with (e - 5) by (unfold e, p0; llia).
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (_ & _ & _ & _ & _ & HSn). fold S in HSn.
    assert (Hrsv20 : rsv < 2^20) by (unfold rsv, e; rewrite Ep; unfold p0; llia).
    assert (He64 : 16 <= p /\ p + n + rsv = e /\ e + 1 <= 2^64 - 2^40) by (unfold rsv, e; rewrite Ep; unfold p0; llia).
    (* [comment removed for export] *)
    assert (GG : forall f, In f (slot_fields mt i (SLive off n)) -> has_grp A f).
    { intros f Hf. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
      exists (Z.to_nat i), (SLive off n). rewrite Z2Nat.id by llia. auto. }
    assert (GF : forall f, In f (slot_fields mt i (SLive off n)) -> has A f) by (intros f Hf; right; right; right; apply GG; exact Hf).
    unfold slot_fields, slot_fields_g in GF, GG. fold Mb S in GF, GG.
    change (slot_start_g Mb S i) with p0 in GG. change (slot_end_g Mb S i) with e in GG. rewrite <- Ep in GG.
    change (e - p - n) with rsv in GG.
    change (slot_start_g Mb S i) with p0 in GF. change (slot_end_g Mb S i) with e in GF. rewrite <- Ep in GF.
    change (e - p - n) with rsv in GF.
    assert (Fe : has A (FCT e 1 0)) by (apply GF; cbn; right; left; reflexivity).
    (* [comment removed for export] *)
    apply (ts_bind_split _ _ s P (fun (r : word) s' => s' = s /\ r = Z_to_bv 64 rsv)).
    { unfold wlit. rewrite c_ltu_Z by llia. rewrite v_srli_Z by llia. change (2^5) with 32.
      replace ((i + 32 * c5) / 32) with c5 by (rewrite Z.mul_comm, Z.div_add by llia; rewrite Z.div_small by llia; llia).
      destruct (i + 32 * c5 <? 160) eqn:Ec.
      - apply Z.ltb_lt in Ec. assert (c5 = rsv) by (subst c5; llia). cbn. split; [reflexivity | f_equal; exact H].
      - apply Z.ltb_ge in Ec. assert (Hc55 : c5 = 5) by llia. assert (Hr5 : 5 <= rsv) by (subst c5; llia).
        rewrite Hc55. apply ts_assert; [reflexivity|].
        assert (F4r : has A (FCT (e - 4) 4 rsv)).
        { apply GF. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
          replace (rsv <? 5) with false by (symmetry; apply Z.ltb_ge; llia). cbn. left. reflexivity. }
        assert (F5r : has A (FCT (e - 5) 1 0)).
        { apply GF. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
          replace (rsv <? 5) with false by (symmetry; apply Z.ltb_ge; llia). cbn. right. left. reflexivity. }
        eapply (ts_lwu_factw A HW _ (ms_mem s) []); [apply repw_init; [exact HW | exact HR] | exact HWIN | exact F4r | apply wfree_range_nil | llia |].
        apply ts_assert; [unfold wlit; rewrite c_ltu_Z by llia; apply Z.ltb_lt; llia|].
        eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact F5r | llia |].
        apply ts_assert; [reflexivity|].
        cbn. split; reflexivity. }
    intros r s1 [-> ->].
    (* [comment removed for export] *)
    rewrite v_sub_Z. apply ts_assert.
    { rewrite c_ltu_Z by llia. replace (e - p <? rsv) with false by (symmetry; apply Z.ltb_ge; llia). reflexivity. }
    rewrite v_sub_Z.
    assert (Fz : has A (FCT (e - rsv) 1 0)).
    { destruct (Z.eq_dec rsv 0) as [E0|E0].
      - rewrite E0, Z.sub_0_r. exact Fe.
      - apply GF. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
        replace (rsv =? 0) with false by (symmetry; apply Z.eqb_neq; llia). cbn. left. reflexivity. }
    eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact Fz | llia |].
    apply ts_assert; [reflexivity|].
    eapply (ts_lbu_fact A HW); [exact HR | exact HWIN | exact Fe | llia |].
    apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    assert (Hspan : forall x, p0 - 4 <= x < e + 1 -> dom A x).
    { intros x Hx. apply (grp_dom A ma mt aib slots x HW Hma Hr). unfold gext_lo, gext_hi. unfold e, p0, S, Mb in *. llia. }
    unfold m_sb, m_sh, m_sw.
    eapply (ts_st_domw A HW _ (ms_mem s) []); [exact RW0 | exact HWIN | llia | intros j Hj; apply Hspan; rewrite Ep in *; unfold p0 in *; llia |].
    pose proof (repw_st_dom A HW s (ms_mem s) [] 1 (p - 3) wm1 RW0 ltac:(llia) ltac:(intros j Hj; apply Hspan; rewrite Ep in *; unfold p0 in *; llia)) as RW1.
    cbn [ms_mem upd] in RW1 |- *. change (bv_unsigned wm1) with (2^64 - 1) in RW1. change (Z.of_nat 1) with 1 in RW1. fold Wh3 in RW1.
    set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (p - 3)) (word_to_le_bytes 1 wm1)) in *.
    replace (p + -2) with (p - 2) by llia.
    eapply (ts_st_domw A HW (upd s m1 (ms_vm s)) (ms_mem s) [Wh3]); [exact RW1 | exact HWIN | llia | intros j Hj; apply Hspan; rewrite Ep in *; unfold p0 in *; llia |].
    pose proof (repw_st_dom A HW (upd s m1 (ms_vm s)) (ms_mem s) [Wh3] 2 (p - 2) w0 RW1 ltac:(llia) ltac:(intros j Hj; apply Hspan; rewrite Ep in *; unfold p0 in *; llia)) as RW2.
    cbn [ms_mem ms_vm upd] in RW2 |- *. change (bv_unsigned w0) with 0 in RW2. change (Z.of_nat 2) with 2 in RW2. fold Wh2 in RW2.
    set (m2 := wbytes m1 (Z_to_bv 64 (p - 2)) (word_to_le_bytes 2 w0)) in *.
    (* [comment removed for export] *)
    assert (Hpm : p <= ma \/ ma + 40 <= p - 3).
    { assert (Gp3 : has_grp A (FCT (p - 3) 1 (i + 32 * c5))).
      { apply GG. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. left. reflexivity. }
      assert (Gp2 : has_grp A (FCT (p - 2) 2 ((p - Mb - 16) / 16))).
      { apply GG. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. cbn. right. left. reflexivity. }
      pose proof (nonmeta_avoid_meta A HW ma mt Hma _ (or_intror (or_intror Gp3))) as H1. cbn in H1.
      pose proof (nonmeta_avoid_meta A HW ma mt Hma _ (or_intror (or_intror Gp2))) as H2. cbn in H2. llia. }
    assert (HWIN2 : WIN (upd s m2 (ms_vm s))) by exact HWIN.
    (* [comment removed for export] *)
    pose proof (w_last_range (mt_w32 mt)) as Hlr.
    assert (Hcnt32 : 2 ^ mt_cnt mt <= 2 ^ 32) by (unfold mt_cnt, mt_last; apply Z.pow_le_mono_r; llia).
    change (ma + 28) with (ma + moff FFreed). change (ma + 24) with (ma + moff FAvail).
    eapply (ts_lw_factw A HW _ (ms_mem s) [Wh2; Wh3]);
      [exact RW2 | exact HWIN2 | right; right; left; exists ma, mt, FFreed; auto
      | repeat apply wfree_range_cons; try apply wfree_range_nil; cbn; llia
      | change (mt_f mt FFreed) with (mt_freed mt); llia |].
    change (mt_f mt FFreed) with (mt_freed mt).
    eapply (ts_lw_factw A HW _ (ms_mem s) [Wh2; Wh3]);
      [exact RW2 | exact HWIN2 | right; right; left; exists ma, mt, FAvail; auto
      | repeat apply wfree_range_cons; try apply wfree_range_nil; cbn; llia
      | change (mt_f mt FAvail) with (mt_avail mt); llia |].
    change (mt_f mt FAvail) with (mt_avail mt).
    pose proof (lor_range32 (mt_avail mt) (mt_freed mt) ltac:(llia) ltac:(llia)) as Hlor.
    assert (Hp2i : 0 <= 2 ^ i < 2 ^ 32) by (split; [llia | apply Z.pow_lt_mono_r; llia]).
    rewrite v_or_w32 by llia. rewrite v_sllw_1 by llia.
    assert (Hbit : Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false).
    { destruct (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i) eqn:E; [| reflexivity].
      exfalso. pose proof (proj1 (Hidle i (SLive off n) Hi Hi0) E). discriminate. }
    apply ts_assert; [rewrite mask_bit_test by llia; rewrite Hbit; reflexivity|].
    (* [comment removed for export] *)
    assert (HNL2 : rdn ml_segs m2 A_NEED_LOCKS 1 = Some [Z_to_bv 8 0]).
    { rewrite <- HNL. rewrite <- (Z_to_bv_bv_unsigned 64 A_NEED_LOCKS). fold NLA. rewrite !rdn1_eq.
      rewrite (rw_frame A (ms_mem s) [Wh2; Wh3] m2 RW2); [reflexivity|].
      pose proof layout_statics.
      repeat apply wfree_cons; try apply wfree_nil; cbn; rewrite uZ by llia; llia. }
    pose proof layout_statics as LST.
    rewrite <- (Z_to_bv_bv_unsigned 64 A_NEED_LOCKS) in HNL2 |- *. fold NLA in HNL2. fold NLA.
    eapply ts_lbu; [apply acc_ok_heap; [exact HWIN2 | llia | llia | ceil; llia] | exact HNL2 |].
    change (bv_unsigned (Z_to_bv 8 0)) with 0.
    (* [comment removed for export] *)
    rewrite is0_w32. rewrite (Z.mod_small (mt_freed mt)) by llia.
    rewrite v_addw_w32. unfold wlit. rewrite v_sllw_2 by llia. rewrite v_addiw_w32.
    change ((mt_w32 mt) mod 32) with (mt_last mt).
    replace (2 ^ (mt_last mt + 1) + -1) with (2 ^ mt_cnt mt - 1) by (unfold mt_cnt; llia).
    rewrite c_eq_w32.
    destruct (add_clear_bit (Z.lor (mt_avail mt) (mt_freed mt)) i (mt_cnt mt)) as [Hlor_eq Hsum];
      [pose proof (lor_range (mt_avail mt) (mt_freed mt) (mt_cnt mt)); llia | llia | exact Hbit |].
    rewrite !Z.mod_small by llia.
    destruct (negb (mt_freed mt =? 0) && negb (Z.lor (mt_avail mt) (mt_freed mt) + 2 ^ i =? 2 ^ mt_cnt mt - 1)) eqn:Eb.
    - (* [comment removed for export] *)
      apply andb_prop in Eb. destruct Eb as [Eb1 Eb2].
      apply Bool.negb_true_iff in Eb1. apply Bool.negb_true_iff in Eb2. apply Z.eqb_neq in Eb1. apply Z.eqb_neq in Eb2.
      apply ts_assert; [reflexivity|].
      rewrite v_addw_w32. fold fr'.
      assert (Hmd : forall j, 0 <= j < 4 -> dom A (ma + moff FFreed + j)).
      { intros j Hj. destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & kk & Hpga & Hkk & Ema).
        left. exists pg. split; [exact Hpga|]. rewrite Ema. unfold meta_addr. cbn. llia. }
      pose proof (dom_addr A HW _ (Hmd 0 ltac:(llia))) as Hd0. pose proof (dom_addr A HW _ (Hmd 3 ltac:(llia))) as Hd3.
      ceil. cbn [moff Z.add] in Hmd, Hd0, Hd3 |- *.
      replace (ma + 28 + 0) with (ma + 28) in Hd0 by llia.
      change (upd (upd s m1 (ms_vm s)) m2 (ms_vm s)) with (upd s m2 (ms_vm s)).
      unfold m_st.
      rewrite (acc_ok_heap (upd s m2 (ms_vm s)) (ma + 28) (Z.of_nat 4) HWIN2); [| llia | llia | ceil; cbn; llia].
      rewrite (st_zone_dom A _ 4 HW ltac:(intros j Hj; apply Hmd; llia) ltac:(llia)).
      change (ms_mem (upd s m2 (ms_vm s))) with m2.
      rewrite (store_ok_domw A (ms_mem s) [Wh2; Wh3] m2 _ 4 RW2 ltac:(intros j Hj; apply Hmd; llia)) by (cbn; llia).
      cbn [andb tsafe ms_vm upd].
      apply HKfast; [| exact Eb1 | exact Eb2].
      pose proof (repw_st_dom A HW (upd s m2 (ms_vm s)) (ms_mem s) [Wh2; Wh3] 4 (ma + 28) (w32 fr') RW2 ltac:(llia) ltac:(intros j Hj; apply Hmd; llia)) as RW3.
      cbn [ms_mem upd Z.of_nat Pos.of_succ_nat Pos.succ] in RW3. change (Z.of_nat 4) with 4 in RW3.
      rewrite u_w32 in RW3. exact RW3.
    - (* [comment removed for export] *)
      apply ts_assert; [reflexivity|].
      apply (HKslow m2 RW2).
      apply Bool.andb_false_iff in Eb. destruct Eb as [Eb | Eb]; apply Bool.negb_false_iff in Eb; apply Z.eqb_eq in Eb; [left | right]; exact Eb.
  Qed.

  (* [comment removed for export] *)
  Lemma free_fast_wf :
    Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false -> mt_freed mt <> 0 -> WF A'.
  Proof using HW Hi Hi0 Hma Hp Hr L' rsv slots'. pu_keep (HW, Hi, Hi0, Hma, Hp, Hr, L', rsv, slots').
    intros Hbit Hfr0.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (Hba : Z.testbit (mt_avail mt) i = false /\ Z.testbit (mt_freed mt) i = false).
    { rewrite Z.lor_spec in Hbit. destruct (Z.testbit (mt_avail mt) i), (Z.testbit (mt_freed mt) i); cbn in Hbit; try discriminate; auto. }
    destruct Hba as [Hba Hbf].
    destruct (add_clear_bit (mt_freed mt) i (mt_cnt mt) Hfd ltac:(llia) Hbf) as [Efr Hfrlt]. fold fr' in Efr, Hfrlt.
    apply (WF_grp_upd A HW ma mt aib slots Hma Hr (mt_avail mt) fr' aib slots' L').
    - apply list_set_length.
    - intros j st st' Hj Hj'. destruct (list_set_nth_inv _ _ _ _ _ Hj') as [(-> & -> & _) | (Hne & Hj2)].
      + rewrite Hi in Hj. injection Hj as <-. right. split; [right; right; exists off, n; reflexivity | left; reflexivity].
      + rewrite Hj in Hj2. injection Hj2 as ->. left. reflexivity.
    - exact Hav.
    - llia.
    - rewrite Efr. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.lor_spec, Z.bits_0, Z.pow2_bits_eqb by llia.
      destruct (Z.eq_dec i j) as [<- | NE].
      + rewrite Hba. reflexivity.
      + replace (i =? j) with false by (symmetry; apply Z.eqb_neq; llia). rewrite orb_false_r.
        pose proof (Z.land_spec (mt_avail mt) (mt_freed mt) j) as X. rewrite Hdis, Z.bits_0 in X. symmetry in X. exact X.
    - exact Haib.
    - exact Havact.
    - exact Haibl.
    - intros j st Hj Hj0. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(Ej & -> & _) | (Hne & Hj2)].
      + assert (j = i) by llia. subst j. split; [reflexivity | intros _].
        rewrite Efr, Z.lor_spec, Z.lor_spec, Z.pow2_bits_true by llia. rewrite !orb_true_r. reflexivity.
      + rewrite <- (Hidle j st Hj2 Hj0).
        rewrite Efr. rewrite !Z.lor_spec, Z.pow2_bits_eqb by llia.
        replace (i =? j) with false by (symmetry; apply Z.eqb_neq; intros ->; apply Hne; reflexivity). rewrite orb_false_r. reflexivity.
    - intros j o k Hj Hj0. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(Ej & E & _) | (Hne & Hj2)]; [discriminate|].
      eapply (wf_live A HW ma mt aib slots j); eauto.
    - intros j Hj. rewrite Efr, Z.lor_spec. rewrite (wf_inactive A HW ma mt aib slots j Hma Hr Hj). reflexivity.
    - intros Hin Hnh. split; [| llia]. exact (proj1 (wf_act_nonhead A HW (mt_sc mt) ma mt Hin Hnh Hma)).
    - intros H; exact H.
    - intros _ _. left. intros E. apply Z.lor_eq_0_iff in E. llia.
    - (* [comment removed for export] *) intros q k. unfold L', lupd. split.
      + intros H. destruct (Z.eq_dec q p) as [-> | Hne]; [discriminate|].
        apply (proj1 (wf_live_map A HW q k)) in H.
        destruct H as (x & mtx & aibx & slx & j & o & Hx & Hrx & Hj0 & Hj & Eq).
        destruct (Z.eq_dec x ma) as [-> | Hxne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          left. exists j, o. split; [exact Hj0|]. split; [| exact Eq].
          unfold slots'. rewrite list_set_nth_other; [exact Hj|]. intros E.
          apply Hne. rewrite Eq, Hp. rewrite <- E, Hi in Hj. injection Hj as -> _. replace j with i by llia. reflexivity.
        * right. exists x, mtx, aibx, slx, j, o. auto 10.
      + intros [(j & o & Hj0 & Hj & Eq) | (x & mtx & aibx & slx & j & o & Hxne & Hx & Hrx & Hj0 & Hj & Eq)].
        * destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(Ej & E & _) | (Hne & Hj2)]; [discriminate|].
          destruct (Z.eq_dec q p) as [-> | Hqp].
          -- exfalso. destruct (live_slot_unique A ma mt aib slots j o k ma mt aib slots i off n HW Hma Hr Hj0 Hj2 Hma Hr Hi0 Hi ltac:(rewrite <- Eq, Hp; reflexivity)) as [_ E]. apply Hne. rewrite E. reflexivity.
          -- apply (proj2 (wf_live_map A HW q k)). exists ma, mt, aib, slots, j, o. auto 10.
        * destruct (Z.eq_dec q p) as [-> | Hqp].
          -- exfalso. destruct (live_slot_unique A x mtx aibx slx j o k ma mt aib slots i off n HW Hx Hrx Hj0 Hj Hma Hr Hi0 Hi ltac:(rewrite <- Eq, Hp; reflexivity)) as [E _]. exact (Hxne E).
          -- apply (proj2 (wf_live_map A HW q k)). exists x, mtx, aibx, slx, j, o. auto 10.
  Qed.

  Lemma free_fast_rep : forall m3,
    Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false ->
    RepW A (ms_mem s) [Wfr; Wh2; Wh3] m3 -> Rep A' m3.
  Proof using HW Hi Hi0 Hma Hp Hr L' MLok rsv slots'. pu_keep (HW, Hi, Hi0, Hma, Hp, Hr, L', MLok, rsv, slots').
    intros m3 Hbit RW3.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16. fold S in HS16.
    fold S in Hfit, Hce. fold Mb in Hal16, Hmem, Hfit, Hce, Hpg.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S) by (subst S; lnia).
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hofit & _). fold S in Hofit.
    assert (Ep : p = p0 + 16 * off) by (rewrite Hp; reflexivity).
    pose proof (meta_clear_of_gext A HW ma mt aib slots Hma Hr) as Hmg. unfold gext_lo, gext_hi in Hmg. fold Mb S in Hmg.
    assert (Hba : Z.testbit (mt_avail mt) i = false /\ Z.testbit (mt_freed mt) i = false).
    { rewrite Z.lor_spec in Hbit. destruct (Z.testbit (mt_avail mt) i), (Z.testbit (mt_freed mt) i); cbn in Hbit; try discriminate; auto. }
    destruct Hba as [Hba Hbf].
    (* [comment removed for export] *)
    assert (CLR : forall f, 0 < f_n f ->
              (f_a f + f_n f <= ma \/ ma + 40 <= f_a f) ->
              (f_a f + f_n f <= p - 3 \/ p <= f_a f) ->
              forall x, f_a f <= x < f_a f + f_n f -> wlook [Wfr; Wh2; Wh3] x = None).
    { intros f Hn' H1 H2 x Hx. apply wlook_free. repeat apply wfree_cons; try apply wfree_nil; cbn; llia. }
    apply (repw_final A A' (ms_mem s) [Wfr; Wh2; Wh3] m3 RW3).
    2:{ intros x Hx. apply (proj1 (dom_grp_upd A ma mt aib slots Hma Hr (mt_avail mt) fr' aib slots' L' x)). exact Hx. }
    intros x b (f & Hf & [Hx ->]).
    destruct (has_grp_upd A ma mt (mt_avail mt) fr' aib slots' L' f Hf) as [[HfA Hor] | [[fl ->] | [Hhdr | (j & st & Hj & Hin)]]].
    - (* [comment removed for export] *)
      right. destruct (other_fact_clear A HW ma mt aib slots Hma Hr f Hor) as (Hn' & Hm' & Hg').
      split; [| exists f; split; [exact HfA | split; [exact Hx | reflexivity]]].
      apply (CLR f Hn' Hm'); [| exact Hx].
      destruct Hg' as [Hg' | (j & ch & Hj & Hlo & Hhi)]; [unfold gext_lo, gext_hi in Hg'; fold Mb S in Hg'; rewrite Ep; unfold p0; llia|].
      (* [comment removed for export] *)
      assert (Hji : Z.of_nat j <> i) by (intros E; rewrite <- E, Nat2Z.id in Hi; rewrite Hi in Hj; discriminate).
      unfold slot_start, slot_end, slot_start_g, slot_end_g in Hlo, Hhi. fold Mb S in Hlo, Hhi.
      rewrite Ep. unfold p0.
      destruct (Z.lt_ge_cases (Z.of_nat j) i) as [Hlt | Hge].
      + left. pose proof (slots_disjoint Mb S (Z.of_nat j) i HS16 ltac:(llia) Hi0 Hlt). llia.
      + right. pose proof (slots_disjoint Mb S i (Z.of_nat j) HS16 Hi0 ltac:(llia) ltac:(llia)). llia.
    - (* [comment removed for export] *)
      destruct (mfield_eq_dec fl FFreed) as [-> | Hne].
      + left. cbn in Hx. rewrite wlook_hit by (cbn; llia). cbn [f_v f_a moff]. f_equal. apply byte_of_sx32. llia.
      + right. pose proof (mfield_range fl) as Hflr. pose proof (mfield_disj fl FFreed Hne) as Hfd'. cbn in Hfd'.
        cbn in Hx. split.
        * apply wlook_free. repeat apply wfree_cons; try apply wfree_nil; cbn; rewrite ?Ep; unfold p0; llia.
        * exists (FCT (ma + moff fl) (mlen fl) (mt_f mt fl)). split; [| split; [exact Hx | cbn; destruct fl; cbn in *; try reflexivity; contradiction]].
          right; right; left. exists ma, mt, fl. auto.
    - (* [comment removed for export] *)
      right. assert (HfA : has A f).
      { right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. left. exact Hhdr. }
      split; [| exists f; split; [exact HfA | split; [exact Hx | reflexivity]]].
      unfold grp_hdr_fields in Hhdr. fold Mb in Hhdr.
      destruct Hhdr as [<- | [<- | []]]; cbn in Hx; (apply wlook_free; repeat apply wfree_cons; try apply wfree_nil; cbn; rewrite ?Ep; unfold p0; llia).
    - (* [comment removed for export] *)
      destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(-> & -> & _) | (Hne & Hj2)].
      + (* [comment removed for export] *)
        right. rewrite Z2Nat.id in Hin by llia. unfold slot_fields, slot_fields_g in Hin. fold Mb S in Hin.
        change (slot_start_g Mb S i) with p0 in Hin. change (slot_end_g Mb S i) with e in Hin.
        cbn [app] in Hin.
        assert (HfA : has A f).
        { right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
          exists (Z.to_nat i), (SLive off n). split; [exact Hi|]. rewrite Z2Nat.id by llia.
          unfold slot_fields, slot_fields_g. fold Mb S. change (slot_start_g Mb S i) with p0. change (slot_end_g Mb S i) with e.
          cbn [app]. destruct Hin as [<- | [<- | []]]; [left; reflexivity | right; left; reflexivity]. }
        split; [| exists f; split; [exact HfA | split; [exact Hx | reflexivity]]].
        destruct Hin as [<- | [<- | []]]; cbn in Hx; (apply wlook_free; repeat apply wfree_cons; try apply wfree_nil; cbn; rewrite ?Ep; unfold e, p0 in *; llia).
      + (* [comment removed for export] *)
        right. assert (HfA : has A f).
        { right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right. exists j, st. auto. }
        split; [| exists f; split; [exact HfA | split; [exact Hx | reflexivity]]].
        pose proof (slot_fact_bounds A HW ma mt aib slots j st f Hma Hr Hj2 Hin) as (B1 & B2).
        pose proof (slot_fields_where A HW ma mt aib slots j st f Hma Hr Hj2 Hin) as (W1 & W2 & W3).
        unfold slot_start, slot_end, slot_start_g, slot_end_g in B1, B2. fold Mb S in B1, B2.
        apply (CLR f ltac:(llia)); [unfold gext_lo, gext_hi in W1, W2; fold Mb S in W1, W2; llia | | exact Hx].
        assert (Hji : Z.of_nat j <> i) by (intros E; apply Hne; rewrite <- E, Nat2Z.id; reflexivity).
        rewrite Ep. unfold p0.
        destruct (Z.lt_ge_cases (Z.of_nat j) i) as [Hlt | Hge].
        * left. pose proof (slots_disjoint Mb S (Z.of_nat j) i HS16 ltac:(llia) Hi0 Hlt). llia.
        * right. pose proof (slots_disjoint Mb S i (Z.of_nat j) HS16 Hi0 ltac:(llia) ltac:(llia)). llia.
  Qed.

  (* [comment removed for export] *)
  Variable pw : word.
  Hypothesis Hpw : bv_unsigned pw = p.

  Lemma free_fast_post : forall m3,
    VMok A (ms_vm s) -> (forall j, 0 <= j < 8 -> ms_mem s (Z_to_bv 64 (LOCKA + j)) = None) ->
    Coh A (ms_mem s) (ms_vm s) -> ACT48 A ->
    RepW A (ms_mem s) [Wfr; Wh2; Wh3] m3 ->
    mt_freed mt <> 0 ->
    free_post A pw s tt (upd s m3 (ms_vm s)).
  Proof using A' HR HW Hi Hi0 Hma Hp Hpw Hr MLok rsv. pu_keep (A', HR, HW, Hi, Hi0, Hma, Hp, Hpw, Hr, MLok, rsv).
    intros m3 HV HL HKc HA48 RW3 Eb1.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16. fold S in HS16.
    fold S in Hfit, Hce. fold Mb in Hal16, Hmem, Hfit, Hce, Hpg.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S) by (subst S; lnia).
    pose proof (wf_live A HW ma mt aib slots i off n Hma Hr Hi Hi0) as (Ho & Hn & Hofit & _). fold S in Hofit.
    assert (Ep : p = p0 + 16 * off) by (rewrite Hp; reflexivity).
    pose proof (grp_heap A ma mt aib slots HW Hma Hr) as (G1 & G2 & G3). unfold gext_lo, gext_hi in G1, G2, G3. fold Mb S in G1, G2, G3.
    ceil.
    destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & kk & Hpga & Hkk & Ema).
    destruct (wf_areas_al A HW pg Hpga) as [Hpgal Hpgh]. unfold heap_range in Hpgh. ceil.
    assert (Hbit : Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = false).
    { destruct (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i) eqn:E; [| reflexivity].
      exfalso. pose proof (proj1 (Hidle i (SLive off n) Hi Hi0) E). discriminate. }
    pose proof (free_fast_wf Hbit Eb1) as HW'. pose proof (free_fast_rep m3 Hbit RW3) as HR'.
    (* [comment removed for export] *)
    assert (CLS : forall x, (ma + 28 <= x < ma + 32) \/ (p - 3 <= x < p) \/ wfree [Wfr; Wh2; Wh3] x).
    { intros x.
      assert (DQrng : (ma + 28) <= x < (ma + 32) \/ (p - 3) <= x < p \/
                     (~ ((ma + 28) <= x < (ma + 32)) /\ ~ ((p - 3) <= x < p))) by lia.
      destruct DQrng as [DQrng | [DQrng | DQrng]];
        [ left; llia
        | right; left; llia |].
       
      right; right; repeat apply wfree_cons; try apply wfree_nil; cbn; llia. }
    assert (OWN1 : forall a : word, ma + 28 <= bv_unsigned a < ma + 32 -> mowned A a).
    { intros a Ha. right. left. exists pg. split; [exact Hpga|]. rewrite Ema in Ha. unfold meta_addr in Ha. llia. }
    assert (OWN2 : forall a : word, p - 3 <= bv_unsigned a < p -> mowned A a).
    { intros a Ha. right. apply (grp_dom A ma mt aib slots _ HW Hma Hr). unfold gext_lo, gext_hi. fold Mb S. rewrite Ep in Ha. unfold p0 in Ha. llia. }
    (* [comment removed for export] *)
    destruct (slot_hdr_facts A HW ma mt aib slots i (SLive off n) off p Hma Hr Hi Hi0 ltac:(left; exists n; reflexivity) Hp) as (c & Hc & F4 & F3 & F2).
    assert (Ffr : has A (FCT (ma + 28) 4 (mt_freed mt))) by (right; right; left; exists ma, mt, FFreed; auto).
    assert (CL : forall (q : word) k x, mlive A q = Some k -> bv_unsigned q <= x < bv_unsigned q + k -> wfree [Wfr; Wh2; Wh3] x).
    { intros q k x Hq Hx. unfold mlive in Hq. apply (proj1 (wf_live_map A HW _ _)) in Hq.
      destruct Hq as (y & mty & aiby & sly & j & o & Hy & Hry & Hj0 & Hj & Eq).
      pose proof (live_clear A HW y mty aiby sly j o k Hy Hry Hj0 Hj) as LC. cbn in LC. rewrite <- Eq in LC.
      pose proof (LC _ Ffr) as X1. pose proof (LC _ F3) as X2. pose proof (LC _ F2) as X3. cbn in X1, X2, X3.
      repeat apply wfree_cons; try apply wfree_nil; cbn; llia. }
    exists A'. split.
    { constructor; [exact HW' | exact HR' | apply (VMok_grp_upd A ma mt aib slots Hma Hr); exact HV | | | exact HA48].
      - intros j Hj. cbn. rewrite (rw_frame A _ _ m3 RW3); [apply HL; exact Hj|].
        destruct (CLS (bv_unsigned (Z_to_bv 64 (LOCKA + j)))) as [X | [X | X]]; [| | exact X]; exfalso; unfold LOCKA in X; rewrite uZ in X by llia; rewrite ?Ema in X; unfold meta_addr in X; rewrite ?Ep in X; unfold p0 in X; llia.
      - (* [comment removed for export] *)
        cbn. apply (coh_restate A A' m3 (ms_vm s)).
        + apply (coh_mem A (ms_mem s) m3 (ms_vm s) HW HV HKc). intros a Ha Hr' Hi'.
          destruct (CLS (bv_unsigned a)) as [X | [X | X]].
          * right. destruct (OWN1 a X) as [G | D]; [exfalso; unfold LOCKA, CTX_END in G; llia | exact D].
          * right. destruct (OWN2 a X) as [G | D]; [exfalso; unfold LOCKA, CTX_END in G; llia | exact D].
          * left. rewrite <- (rw_frame A _ _ m3 RW3 a X). exact Ha.
        + reflexivity.
        + reflexivity.
        + intros sc Hsc2. reflexivity.
        + intros x mt' Hx. unfold A' in Hx. cbn in Hx. unfold aupd in Hx.
          destruct (Z.eq_dec x ma) as [-> | Hne].
          * injection Hx as <-. exists mt. split; [exact Hma|]. cbn. split; intros HH; discriminate HH.
          * exists mt'. split; [exact Hx|]. split; intros HH; exact HH.
        + intros sc x Hsc2. unfold meta_usage, A'. cbn. unfold aupd.
          destruct (Z.eq_dec x ma) as [-> | Hne]; [| reflexivity].
          rewrite Hma, Hr. cbn. reflexivity. }
    split; [reflexivity|]. split; [reflexivity|].
    assert (Elive : forall q, mlive A' q = if Z.eq_dec (bv_unsigned q) p then None else mlive A q).
    { intros q. reflexivity. }
    split. { rewrite Elive, Hpw. destruct (Z.eq_dec p p); [reflexivity | contradiction]. }
    split. { intros q Hq. rewrite Elive. destruct (Z.eq_dec (bv_unsigned q) p) as [E|NE]; [| reflexivity].
             exfalso. apply Hq. apply bv_eq. rewrite E, Hpw. reflexivity. }
    split.
    { intros a Hown Hown' Herr. cbn. apply (rw_frame A _ _ m3 RW3).
      destruct (CLS (bv_unsigned a)) as [X | [X | X]]; [exfalso; exact (Hown (OWN1 a X)) | exfalso; exact (Hown (OWN2 a X)) | exact X]. }
    split.
    { intros q k j Hq Hj. cbn. apply (rw_frame A _ _ m3 RW3).
      rewrite Elive in Hq. destruct (Z.eq_dec (bv_unsigned q) p); [discriminate|].
      pose proof (m_live_hull A (ms_mem s) (ms_vm s) q k ltac:(constructor; assumption) Hq) as (Hk & _ & Hce' & _).
      pose proof (round16_ge k). ceil. pose proof (u64_range q).
      apply (CL q k); [exact Hq|]. unfold at_. rewrite uZ by llia. llia. }
    split. { intros a Hm. right. cbn. apply (rw_mapped A _ _ m3 RW3). exact Hm. }
    split; [repeat split; reflexivity | cbn; llia].
  Qed.
End FreeLive.

(* [comment removed for export] *)

End WithLayout.
