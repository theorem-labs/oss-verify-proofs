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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_tables MallocInv_steps MallocInv_enframe_tail.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition off_cycle (SL O1 : Z) : Z :=
  let m1 := Z.lor SL (SL / 2) in
  let m2 := Z.lor (m1 / 4) m1 in
  let m3 := Z.lor (m2 / 16) m2 in
  let o2 := Z.land O1 m3 in
  if SL <? o2 then o2 - SL - 1 else o2.

Definition off_cycle_ok (SL O1 : Z) : bool :=
  let o := off_cycle SL O1 in (0 <=? o) && (o <=? SL).

Lemma off_cycle_all : forallb (fun SL => forallb (fun O1 => negb (SL <? O1) || off_cycle_ok SL O1) (Zseq 0 256)) (Zseq 0 255) = true.
Proof using Type. pu_keep tt. vm_compute. reflexivity. Qed.

Lemma off_cycle_bound : forall SL O1, 0 <= SL -> SL < O1 <= 255 -> 0 <= off_cycle SL O1 <= SL.
Proof using Type. pu_keep tt.
  intros SL O1 H1 H2.
  pose proof (proj1 (forallb_forall _ _) off_cycle_all SL (Zseq_In 255 0 SL ltac:(llia))) as H. cbn beta in H.
  pose proof (proj1 (forallb_forall _ _) H O1 (Zseq_In 256 0 O1 ltac:(llia))) as H'. cbn beta in H'.
  apply Bool.orb_true_iff in H'. destruct H' as [H' | H'].
  - apply Bool.negb_true_iff in H'. apply Z.ltb_ge in H'. llia.
  - unfold off_cycle_ok in H'. apply andb_prop in H'. destruct H' as [Ha Hb].
    apply Z.leb_le in Ha. apply Z.leb_le in Hb. llia.
Qed.

(* [comment removed for export] *)
Lemma lor_bound : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof using Type. pu_keep tt.
  intros a b n Ha Hb. split; [apply Z.lor_nonneg; llia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [-> | Hnz]; [llia|].
  assert (Hn : 0 <= n \/ n < 0) by llia. destruct Hn as [Hn|Hn]; [| rewrite Z.pow_neg_r in Ha by llia; llia].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); llia|].
  rewrite Z.log2_lor by llia.
  destruct (Z.eq_dec a 0) as [-> | Ha0]; destruct (Z.eq_dec b 0) as [-> | Hb0].
  - exfalso. apply Hnz. reflexivity.
  - rewrite Z.max_r by (pose proof (Z.log2_nonneg b); rewrite Z.log2_nonpos by llia; llia). apply Z.log2_lt_pow2; llia.
  - rewrite Z.max_l by (pose proof (Z.log2_nonneg a); rewrite Z.log2_nonpos by llia; llia). apply Z.log2_lt_pow2; llia.
  - apply Z.max_lub_lt; apply Z.log2_lt_pow2; llia.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall a, 0 <= a < 2^64 -> Z.lxor a (2^64 - 1) = 2^64 - 1 - a.
Proof using Type. pu_keep tt.
  intros a Ha. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec. change (2^64 - 1) with (Z.ones 64) at 1. rewrite Z.testbit_ones by llia.
  assert (E : 2^64 - 1 - a = Z.lnot a + 2^64) by (unfold Z.lnot; llia). rewrite E.
  destruct (Z.lt_ge_cases i 64) as [Hl | Hl].
  - replace ((0 <=? i) && (i <? 64))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; llia).
    rewrite <- (Z.mod_pow2_bits_low (Z.lnot a + 2^64) 64 i) by llia.
    rewrite <- Z.add_mod_idemp_r by llia. rewrite Z.mod_same by llia. rewrite Z.add_0_r.
    rewrite Z.mod_pow2_bits_low by llia. rewrite Z.lnot_spec by llia. apply xorb_true_r.
  - replace ((0 <=? i) && (i <? 64))%bool with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; llia).
    rewrite xorb_false_r. rewrite (testbit_above64 a) by llia. symmetry. apply testbit_above64; llia.
Qed.

Lemma swrap32_add_2p64 : forall z, bv_swrap 32 (2^64 + z) = bv_swrap 32 z.
Proof using Type. pu_keep tt.
  intros z. rewrite !swrap32_eq. f_equal.
  replace (2^64 + z + 2^31) with (z + 2^31 + 2^32 * 2^32) by llia. rewrite Z.mod_add by llia. reflexivity.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof using Type. pu_keep tt.
  intros a b Ha Hb.
  assert (Hd : Z.land (Z.land a b) (Z.ldiff a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hd) as E.
  rewrite Z.lxor_lor in E by exact Hd. rewrite Z.lor_comm, Z.lor_ldiff_and in E.
  pose proof (Z.ldiff_nonneg a b). llia.
Qed.

Section Enframe.
  Context {R : Type}.
  Variables (A : astate) (s : mstate).
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i nn : Z) (ctr : word).
  Hypothesis HW : WF A.
  Hypothesis HR : Rep A (ms_mem s).
  Hypothesis HWIN : WIN s.
  Hypothesis HRO : rodata_clear (ms_mem s).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hnn : 0 <= nn /\ nn + 4 <= mt_stride mt /\ mt_stride mt - nn < 2^20.

  Let S := mt_stride mt.
  Let Mb := mt_mem mt.
  Let p0 := Mb + 16 + i * S.
  Let e := p0 + S - 4.
  Let SL := (S - nn - 4) / 16.

  Definition enframe_post (k : word -> M R) (P : R -> mstate -> Prop) : Prop :=
    forall off s',
      0 <= off <= SL ->
      let A' := slot_set A ma i (SLive off nn) (lupd (a_live A) (p0 + 16 * off) (Some nn)) in
      WF A' -> Rep A' (ms_mem s') ->
      WIN s' -> ms_vm s' = ms_vm s -> ms_lo s' = ms_lo s -> ms_hi s' = ms_hi s ->
      rodata_clear (ms_mem s') ->
      (forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> ms_mem s' a = ms_mem s a) ->
      (* [comment removed for export] *)
      (forall a : word, p0 + 16 * off <= bv_unsigned a < p0 + 16 * off + nn -> ms_mem s' a = ms_mem s a) ->
      tsafe (k (Z_to_bv 64 (p0 + 16 * off)) s') P.

  Theorem enframe_ok : forall (k : word -> M R) P,
    enframe_post k P ->
    tsafe ((x <- m_enframe (Z_to_bv 64 ma) (Z_to_bv 64 i) (Z_to_bv 64 nn) ctr ;; k x) s) P.
  Proof using HR HRO HW HWIN Hi Hi0 Hma Hnn Hr MLok. pu_keep (HR, HRO, HW, HWIN, Hi, Hi0, Hma, Hnn, Hr, MLok).
    intros k P HK.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16.
    fold S in HS16, Hfit, Hce, Hnn. fold Mb in Hal16, Hmem, Hce, Hpg.
    assert (Ep0 : p0 = Mb + 16 + i * S) by reflexivity.
    assert (Ee : e = p0 + S - 4) by reflexivity.
    assert (ESL : SL = (S - nn - 4) / 16) by reflexivity.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    assert (Hic : i < mt_cnt mt) by llia.
    assert (Hi32 : i < 32) by (unfold mt_cnt, mt_last in Hic; pose proof (w_last_range (mt_w32 mt)); llia).
    assert (HiS : 0 <= i * S /\ i * S + S <= mt_cnt mt * S) by (unfold S; lnia).
    ceil.
    (* [comment removed for export] *)
    pose proof (iS_small A ma mt aib slots i HW Hma Hr ltac:(llia)) as HiSsmall. fold S in HiSsmall.
    pose proof (grp_dom A ma mt aib slots) as Hdom.
    assert (Hspan : forall x, p0 - 4 <= x < e + 1 -> dom A x).
    { intros x Hx. apply (Hdom x HW Hma Hr). unfold gext_lo, gext_hi. unfold e, p0, S, Mb in *. llia. }
    pose proof (span_clear A HW ma mt aib slots i STaken Hma Hr Hi Hi0 (or_intror eq_refl)) as Hclear.
    unfold slot_start, slot_end, slot_start_g, slot_end_g in Hclear. fold Mb S in Hclear.
    (* [comment removed for export] *)
    unfold m_enframe. reassoc; rewrite at_Z. change (ma + 32) with (ma + moff FW32).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | unfold mt_w32 in Hw32; exact Hw32 |].
    fold (mt_w32 mt). reassoc.
    eapply (ts_get_stride A HW); [exact HR | exact HWIN | exact HRO | exact Hma | exact Hr |]. fold S.
    reassoc; rewrite at_Z. change (ma + 16) with (ma + moff FMem).
    eapply (ts_ld_meta A HW); [exact HR | exact HWIN | exact Hma | reflexivity | unfold mt_mem in *; unfold Mb in *; llia |].
    fold (mt_mem mt). fold Mb.
    reassoc. rewrite v_mul_Z, v_add_Z, at_Z.
    (* [comment removed for export] *)
    replace (Mb + S * i + 13) with (p0 - 3) by (unfold p0; llia).
    eapply (ts_lbu_dom A HW); [exact HR | exact HWIN | apply Hspan; llia |]. intros b13 Hb13.
    reassoc.
    apply (ts_bind_split _ _ s P (fun (o : word) s' => s' = s)).
    { rewrite is0_Z by llia. destruct (b13 =? 0).
      - exact eq_refl.
      - rewrite !at_Z. replace (Mb + S * i + 16 + -2) with (p0 - 2) by (unfold p0; llia).
        eapply (ts_lhu_dom A HW); [exact HR | exact HWIN | apply Hspan; llia | apply Hspan; llia |].
        intros v Hv. exact eq_refl. }
    intros off0 s' ->.
    (* [comment removed for export] *)
    reassoc; rewrite !at_Z. replace (Mb + S * i + 16 + -4) with (p0 - 4) by (unfold p0; llia).
    eapply (ts_lbu_fact A HW _ (p0 - 4) 0); [exact HR | exact HWIN | | llia |].
    { right; right; right. exists ma, mt, aib, slots. split; [exact Hma | split; [exact Hr|]]. right.
      exists (Z.to_nat i), STaken. split; [exact Hi|]. rewrite Z2Nat.id by llia.
      unfold slot_fields, slot_fields_g, slot_start_g. cbn. left. rewrite Ep0. reflexivity. }
    reassoc. apply ts_assert; [reflexivity|].
    (* [comment removed for export] *)
    reassoc.
    assert (HSL : 0 <= SL /\ 16 * SL <= S - nn - 4) by (unfold SL; split; [apply Z.div_pos; llia | ]; pose proof (Z.mul_div_le (S - nn - 4) 16 ltac:(llia)); llia).
    assert (HSLhi : SL < 2^20) by (unfold SL; apply Z.div_lt_upper_bound; llia).
    set (O1 := Z.land (bv_unsigned off0) 255).
    assert (HO1 : 0 <= O1 <= 255).
    { subst O1. split; [apply Z.land_nonneg; right; llia|].
      change 255 with (Z.ones 8). rewrite Z.land_ones by llia. pose proof (Z.mod_pos_bound (bv_unsigned off0) (2^8) ltac:(llia)). change (Z.ones 8) with (2^8 - 1). llia. }
    apply (ts_bind_split _ _ s P (fun (o : word) s' => s' = s /\ exists OFF, o = Z_to_bv 64 OFF /\ 0 <= OFF <= SL /\ OFF <= 255)).
    { rewrite (v_sub_Z S nn), v_addi_Z. replace (S - nn + -4) with (S - nn - 4) by llia.
      rewrite v_srli_Z by llia. change (2^4) with 16. fold SL.
      rewrite <- (Z_to_bv_bv_unsigned 64 off0). rewrite v_andi_Z by (pose proof (u64_range off0); llia). fold O1.
      rewrite c_ltu_Z by llia.
      destruct (SL <? O1) eqn:Hlt; cbn [negb].
      - (* [comment removed for export] *) apply Z.ltb_lt in Hlt.
        assert (HSL254 : SL <= 254) by llia.
        rewrite v_srli_Z by llia. change (2^5) with 32.
        replace ((S - nn - 4) / 32) with (SL / 2) by (unfold SL; rewrite Z.div_div by llia; reflexivity).
        assert (B1 : 0 <= SL / 2 < 2^8) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
        pose proof (lor_bound SL (SL / 2) 8 ltac:(llia) B1) as Bm1.
        rewrite v_or_Z by llia. set (m1 := Z.lor SL (SL / 2)) in *.
        assert (B2 : 0 <= m1 / 4 < 2^8) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
        pose proof (lor_bound (m1 / 4) m1 8 B2 ltac:(llia)) as Bm2.
        rewrite v_srli_Z by llia. change (2^2) with 4. rewrite v_or_Z by llia. set (m2 := Z.lor (m1 / 4) m1) in *.
        assert (B3 : 0 <= m2 / 16 < 2^8) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
        pose proof (lor_bound (m2 / 16) m2 8 B3 ltac:(llia)) as Bm3.
        rewrite v_srli_Z by llia. change (2^4) with 16. rewrite v_or_Z by llia. set (m3 := Z.lor (m2 / 16) m2) in *.
        assert (Bo2 : 0 <= Z.land O1 m3 <= O1).
        { split; [apply Z.land_nonneg; llia | apply land_le_l; llia]. }
        rewrite v_and_Z by llia. set (o2 := Z.land O1 m3) in *.
        rewrite v_sltu_Z by llia.
        pose proof (off_cycle_bound SL O1 ltac:(llia) ltac:(llia)) as Hoc.
        assert (Eoc : off_cycle SL O1 = if SL <? o2 then o2 - SL - 1 else o2) by reflexivity.
        destruct (SL <? o2) eqn:Hlt2.
        + apply Z.ltb_lt in Hlt2.
          rewrite w0_eq, v_subw_Z by llia. rewrite swrap32_small by llia. change (0 - 1) with (-1).
          rewrite <- (ZZ_mod (-1)). change ((-1) mod 2^64) with (2^64 - 1).
          rewrite v_xori_negZ by llia. change (2^64 + -1) with (2^64 - 1). rewrite lxor_ones64 by llia.
          rewrite v_and_Z by llia. rewrite (Z.land_comm (2^64 - 1)).
          change (Z.land (2^64 - 1 - SL) (2^64 - 1)) with (Z.land (2^64 - 1 - SL) (Z.ones 64)).
          rewrite Z.land_ones_low; [| llia | ].
          2:{ destruct (Z.eq_dec (2^64 - 1 - SL) 0) as [->|]; [cbn; llia|]. apply Z.log2_lt_pow2; llia. }
          rewrite v_addw_Z by llia. replace (2^64 - 1 - SL + o2) with (2^64 + (o2 - SL - 1)) by llia.
          rewrite swrap32_add_2p64, swrap32_small by llia.
          rewrite c_ltu_Z by llia. replace (SL <? o2 - SL - 1) with false by (symmetry; apply Z.ltb_ge; llia).
          cbn [negb]. apply ts_assert; [reflexivity|]. cbn.
          split; [reflexivity|]. exists (o2 - SL - 1). split; [reflexivity | llia].
        + apply Z.ltb_ge in Hlt2.
          rewrite w0_eq, v_subw_Z by llia. rewrite swrap32_small by llia. change (0 - 0) with 0.
          rewrite v_xori_negZ by llia. change (2^64 + -1) with (2^64 - 1). rewrite lxor_ones64 by llia.
          rewrite v_and_Z by llia. rewrite Z.land_0_l.
          rewrite v_addw_Z by llia. rewrite Z.add_0_l, swrap32_small by llia.
          rewrite c_ltu_Z by llia. replace (SL <? o2) with false by (symmetry; apply Z.ltb_ge; llia).
          cbn [negb]. apply ts_assert; [reflexivity|]. cbn.
          split; [reflexivity|]. exists o2. split; [reflexivity | llia].
      - apply Z.ltb_ge in Hlt. cbn. split; [reflexivity|]. exists O1. split; [reflexivity | llia]. }
    intros offw s' (-> & OFF & -> & HOFF & HOFF255).
    set (Pp := p0 + 16 * OFF).
    assert (HPp : p0 <= Pp /\ Pp + nn <= e) by (unfold Pp, e; llia).
    (* [comment removed for export] *)
    reassoc. rewrite is0_Z by llia.
    rewrite v_slliw_Z by llia. change (2^4) with 16. rewrite swrap32_small by llia. rewrite v_add_Z, at_Z.
    replace (Mb + S * i + 16 + 16 * OFF) with Pp by (unfold Pp; llia).
    replace (Mb + S * i + 16 + OFF * 16) with Pp by (unfold Pp; llia).
    replace (Mb + S * i + 16 + -3) with (p0 - 3) by llia.
    replace (Mb + S * i + 16 + -2) with (p0 - 2) by llia.
    replace (Mb + S * i + 16) with p0 by llia.
    set (INV1 := fun (s1 : mstate) =>
      Rep A (ms_mem s1) /\ WIN s1 /\ ms_vm s1 = ms_vm s /\ ms_lo s1 = ms_lo s /\ ms_hi s1 = ms_hi s /\
      rodata_clear (ms_mem s1) /\
      (forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> ms_mem s1 a = ms_mem s a) /\
      (forall a : word, Pp <= bv_unsigned a < Pp + nn -> ms_mem s1 a = ms_mem s a) /\
      (OFF <> 0 -> mbyte (ms_mem s1) (p0 - 3) = Some 224 /\ mbyte (ms_mem s1) (p0 - 2) = Some (OFF mod 256) /\
                   mbyte (ms_mem s1) (p0 - 1) = Some (OFF / 256) /\ mbyte (ms_mem s1) (Pp - 4) = Some 0)).
    apply (ts_bind_split _ _ s P (fun r s1 => r = (Z_to_bv 64 Pp, Z_to_bv 64 Mb) /\ INV1 s1)).
    { destruct (OFF =? 0) eqn:EO.
      - apply Z.eqb_eq in EO. cbn. split; [f_equal; apply f_equal; unfold Pp; llia|].
        subst INV1. cbn beta.
        split; [exact HR|]. split; [exact HWIN|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact HRO|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. intros HO. llia.
      - apply Z.eqb_neq in EO.
        assert (HPp16 : p0 + 16 <= Pp) by (unfold Pp; llia).
        eapply (ts_st_clear A HW); [exact HR | exact HWIN | llia | intros j Hj; apply Hspan; llia
          | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
        intros HR1. cbn [ms_mem ms_vm upd].
        eapply (ts_st_clear A HW); [exact HR1 | apply WIN_upd; exact HWIN | llia | intros j Hj; apply Hspan; llia
          | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat Pos.to_nat]; llia |].
        intros HR2. cbn [ms_mem ms_vm upd].
        replace (Pp + -4) with (Pp - 4) by llia.
        eapply (ts_st_clear A HW); [exact HR2 | apply WIN_upd; exact HWIN | llia | intros j Hj; apply Hspan; llia
          | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
        intros HR3. cbn [ms_mem ms_vm upd].
        eapply (ts_ld_meta A HW); [exact HR3 | apply WIN_upd; exact HWIN | exact Hma | reflexivity | unfold mt_mem in *; unfold Mb in *; llia |].
        fold (mt_mem mt). fold Mb. apply ts_ret.
        split; [reflexivity|].
        subst INV1. cbn beta. cbn [ms_mem ms_vm ms_lo ms_hi upd].
        assert (Hlen1 : length (word_to_le_bytes 1 (wlit (2 ^ 64 - 32))) = 1%nat) by reflexivity.
        assert (Hlen2 : length (word_to_le_bytes 2 (Z_to_bv 64 OFF)) = 2%nat) by reflexivity.
        assert (Hlen3 : length (word_to_le_bytes 1 w0) = 1%nat) by reflexivity.
        pose proof (dom_addr A HW (p0 - 4) ltac:(apply Hspan; llia)) as Hlo4.
        pose proof (dom_addr A HW e ltac:(apply Hspan; llia)) as Hhie. ceil.
        split; [exact HR3|]. split; [apply WIN_upd; exact HWIN|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        pose proof (grp_heap A ma mt aib slots HW Hma Hr) as Hheap. unfold gext_lo, gext_hi in Hheap. fold Mb S in Hheap.
        split.
        { apply rodata_clear_wbytes; [| llia | rewrite Hlen3; cbn [Z.of_nat]; llia | rewrite Hlen3; cbn [Z.of_nat]; llia].
          apply rodata_clear_wbytes; [| llia | rewrite Hlen2; cbn [Z.of_nat]; llia | rewrite Hlen2; cbn [Z.of_nat]; llia].
          apply rodata_clear_wbytes; [exact HRO | llia | rewrite Hlen1; cbn [Z.of_nat]; llia | rewrite Hlen1; cbn [Z.of_nat]; llia]. }
        split.
        { intros a Ha. pose proof (u64_range a).
          rewrite (wbytes_other_Z _ (Pp - 4)) by (rewrite ?Hlen3; cbn [Z.of_nat]; llia).
          rewrite (wbytes_other_Z _ (p0 - 2)) by (rewrite ?Hlen2; cbn [Z.of_nat]; llia).
          rewrite (wbytes_other_Z _ (p0 - 3)) by (rewrite ?Hlen1; cbn [Z.of_nat]; llia). reflexivity. }
        split.
        { intros a Ha. pose proof (u64_range a).
          rewrite (wbytes_other_Z _ (Pp - 4)) by (rewrite ?Hlen3; cbn [Z.of_nat]; llia).
          rewrite (wbytes_other_Z _ (p0 - 2)) by (rewrite ?Hlen2; cbn [Z.of_nat]; llia).
          rewrite (wbytes_other_Z _ (p0 - 3)) by (rewrite ?Hlen1; cbn [Z.of_nat]; llia). reflexivity. }
        intros _.
        assert (E224 : byte_of (bv_unsigned (wlit (2 ^ 64 - 32))) 0 = 224) by reflexivity.
        repeat split.
        + rewrite (mbyte_store_out _ (Pp - 4)) by (cbn [Z.of_nat]; llia).
          rewrite (mbyte_store_out _ (p0 - 2)) by (cbn [Z.of_nat]; llia).
          replace (p0 - 3) with (p0 - 3 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia). rewrite E224. reflexivity.
        + rewrite (mbyte_store_out _ (Pp - 4)) by (cbn [Z.of_nat]; llia).
          replace (p0 - 2) with (p0 - 2 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
          rewrite byte_of_0, uZ by llia. reflexivity.
        + rewrite (mbyte_store_out _ (Pp - 4)) by (cbn [Z.of_nat]; llia).
          replace (p0 - 1) with (p0 - 2 + 1) by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
          rewrite byte_of_1, uZ by llia. rewrite (Z.mod_small (OFF / 256)) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]). reflexivity.
        + replace (Pp - 4) with (Pp - 4 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
          rewrite byte_of_0. reflexivity. }
    intros r s1 (-> & HI1).
    destruct HI1 as (HR1 & HWIN1 & Hvm1 & Hlo1 & Hhi1 & HRO1 & Hfr1 & Hpay1 & Hhdr1).
    cbv iota beta.
    pose proof (grp_heap A ma mt aib slots HW Hma Hr) as Hheap. unfold gext_lo, gext_hi in Hheap. fold Mb S in Hheap.
    ceil.
    set (RSV := e - nn - Pp).
    assert (HRSV : 0 <= RSV < 2^20) by (unfold RSV; llia).
    set (OFU := (Pp - Mb - 16) / 16).
    assert (HOFU : 0 <= OFU < 2^20).
    { unfold OFU. split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]. }
    (* [comment removed for export] *)
    rewrite !at_Z. rewrite (v_subw_Z Pp Mb) by llia. rewrite swrap32_small by llia.
    rewrite v_addi_Z, (v_srli_Z (Pp - Mb + -16)) by llia. change (2^4) with 16.
    replace ((Pp - Mb + -16) / 16) with OFU by (unfold OFU; f_equal; llia).
    rewrite (v_add_Z p0 S), v_addi_Z, (v_add_Z nn Pp).
    rewrite (v_subw_Z (p0 + S + -4) (nn + Pp)) by llia. rewrite swrap32_small by llia.
    replace (p0 + S + -4 - (nn + Pp)) with RSV by (unfold RSV; llia).
    replace (p0 + S + -4) with e by llia.
    rewrite is0_Z by llia. rewrite w0_eq, (v_subw_Z 0 RSV) by llia. rewrite swrap32_small by llia.
    rewrite (v_add_Z e (0 - RSV)). replace (e + (0 - RSV)) with (Pp + nn) by (unfold RSV; llia).
    unfold wlit. rewrite c_lts_Z by llia.
    replace (Pp + -3) with (Pp - 3) by llia. replace (Pp + -2) with (Pp - 2) by llia.
    rewrite !at_Z. replace (p0 + S + -9) with (e - 5) by llia. replace (p0 + S + -8) with (e - 4) by llia.
    (* [comment removed for export] *)
    reassoc.
    eapply (ts_st_clear A HW); [exact HR1 | exact HWIN1 | llia | intros j Hj; apply Hspan; llia
      | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
    intros HR2. cbn [ms_mem ms_vm upd]. reassoc.
    eapply (ts_st_clear A HW); [exact HR2 | apply WIN_upd; exact HWIN1 | llia | intros j Hj; apply Hspan; llia
      | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat Pos.to_nat]; llia |].
    intros HR3. cbn [ms_mem ms_vm upd]. reassoc.
    set (m3 := wbytes (wbytes (ms_mem s1) (Z_to_bv 64 (Pp - 3)) (word_to_le_bytes 1 (Z_to_bv 64 i)))
                      (Z_to_bv 64 (Pp - 2)) (word_to_le_bytes 2 (Z_to_bv 64 OFU))) in *.
    set (s3 := upd s1 m3 (ms_vm s1)).
    (* [comment removed for export] *)
    set (INV2 := fun (s2 : mstate) =>
      Rep A (ms_mem s2) /\ WIN s2 /\ ms_vm s2 = ms_vm s /\ ms_lo s2 = ms_lo s /\ ms_hi s2 = ms_hi s /\
      rodata_clear (ms_mem s2) /\
      (forall a : word, bv_unsigned a < p0 - 3 \/ e <= bv_unsigned a -> ms_mem s2 a = ms_mem s a) /\
      (forall a : word, Pp <= bv_unsigned a < Pp + nn -> ms_mem s2 a = ms_mem s a) /\
      (OFF <> 0 -> mbyte (ms_mem s2) (p0 - 3) = Some 224 /\ mbyte (ms_mem s2) (p0 - 2) = Some (OFF mod 256) /\
                   mbyte (ms_mem s2) (p0 - 1) = Some (OFF / 256) /\ mbyte (ms_mem s2) (Pp - 4) = Some 0) /\
      mbyte (ms_mem s2) (Pp - 3) = Some i /\
      mbyte (ms_mem s2) (Pp - 2) = Some (OFU mod 256) /\ mbyte (ms_mem s2) (Pp - 1) = Some ((OFU / 256) mod 256) /\
      (RSV <> 0 -> mbyte (ms_mem s2) (Pp + nn) = Some 0) /\
      (5 <= RSV -> mbyte (ms_mem s2) (e - 5) = Some 0 /\
                  forall kk, 0 <= kk < 4 -> mbyte (ms_mem s2) (e - 4 + kk) = Some (byte_of RSV kk))).
    (* [comment removed for export] *)
    assert (Hm3fr : forall a : word, bv_unsigned a < Pp - 3 \/ Pp <= bv_unsigned a -> m3 a = ms_mem s1 a).
    { intros a Ha. unfold m3. pose proof (u64_range a).
      rewrite (wbytes_other_Z _ (Pp - 2)) by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia).
      rewrite (wbytes_other_Z _ (Pp - 3)) by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia). reflexivity. }
    assert (Hm3out : forall x, 0 <= x < 2^64 -> (x < Pp - 3 \/ Pp <= x) -> mbyte m3 x = mbyte (ms_mem s1) x).
    { intros x Hx Hout. unfold m3.
      rewrite (mbyte_store_out _ (Pp - 2)) by (cbn [Z.of_nat]; llia).
      rewrite (mbyte_store_out _ (Pp - 3)) by (cbn [Z.of_nat]; llia). reflexivity. }
    assert (Hm3i : mbyte m3 (Pp - 3) = Some i).
    { unfold m3. rewrite (mbyte_store_out _ (Pp - 2)) by (cbn [Z.of_nat]; llia).
      replace (Pp - 3) with (Pp - 3 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
      rewrite byte_of_0, uZ by llia. rewrite Z.mod_small by llia. reflexivity. }
    assert (Hm3o0 : mbyte m3 (Pp - 2) = Some (OFU mod 256)).
    { unfold m3. replace (Pp - 2) with (Pp - 2 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
      rewrite byte_of_0, uZ by llia. reflexivity. }
    assert (Hm3o1 : mbyte m3 (Pp - 1) = Some ((OFU / 256) mod 256)).
    { unfold m3. replace (Pp - 1) with (Pp - 2 + 1) by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia).
      rewrite byte_of_1, uZ by llia. reflexivity. }
    assert (HRO3 : rodata_clear m3).
    { unfold m3. apply rodata_clear_wbytes; [| llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia].
      apply rodata_clear_wbytes; [exact HRO1 | llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia]. }
    assert (BASE2 : forall m2, Rep A m2 -> rodata_clear m2 ->
              (forall x, 0 <= x < 2^64 -> (x < Pp + nn \/ e <= x) -> mbyte m2 x = mbyte m3 x) ->
              (forall a : word, bv_unsigned a < Pp + nn \/ e <= bv_unsigned a -> m2 a = m3 a) ->
              (RSV <> 0 -> mbyte m2 (Pp + nn) = Some 0) ->
              (5 <= RSV -> mbyte m2 (e - 5) = Some 0 /\ forall kk, 0 <= kk < 4 -> mbyte m2 (e - 4 + kk) = Some (byte_of RSV kk)) ->
              INV2 (upd s1 m2 (ms_vm s1))).
    { intros m2 HRm2 HROm2 Hmb2 Hfr2 Hz2 Hf2. subst INV2. cbn beta. cbn [ms_mem ms_vm ms_lo ms_hi upd].
      split; [exact HRm2|]. split; [apply WIN_upd; exact HWIN1|]. split; [exact Hvm1|]. split; [exact Hlo1|]. split; [exact Hhi1|].
      split; [exact HROm2|].
      split. { intros a Ha. rewrite Hfr2 by llia. rewrite Hm3fr by llia. apply Hfr1. exact Ha. }
      split. { intros a Ha. rewrite Hfr2 by llia. rewrite Hm3fr by llia. apply Hpay1. exact Ha. }
      split. { intros HO. destruct (Hhdr1 HO) as (B1 & B2 & B3 & B4).
               rewrite !Hmb2 by llia. rewrite !Hm3out by llia. auto. }
      split. { rewrite Hmb2 by llia. exact Hm3i. }
      split. { rewrite Hmb2 by llia. exact Hm3o0. }
      split. { rewrite Hmb2 by llia. exact Hm3o1. }
      split; [exact Hz2 | exact Hf2]. }
    apply (ts_bind_split _ _ s3 P (fun c s2 => c = Z_to_bv 64 (Z.min RSV 5) /\ INV2 s2)).
    { destruct (RSV =? 0) eqn:ER.
      - apply Z.eqb_eq in ER. apply ts_ret. split; [rewrite ER; reflexivity|].
        apply BASE2; [exact HR3 | exact HRO3 | intros; reflexivity | intros; reflexivity | intros HZ; llia | intros H5; llia].
      - apply Z.eqb_neq in ER.
        eapply (ts_st_clear A HW); [exact HR3 | apply WIN_upd; exact HWIN1 | llia | intros j Hj; apply Hspan; llia
          | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
        intros HR4. cbn [ms_mem ms_vm upd].
        destruct (RSV <? 5) eqn:ER5.
        + apply Z.ltb_lt in ER5. apply ts_ret. split; [rewrite Z.min_l by llia; reflexivity|].
          apply BASE2; [exact HR4 | | | | |].
          * apply rodata_clear_wbytes; [exact HRO3 | llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia].
          * intros x Hx Hout. apply mbyte_store_out; cbn [Z.of_nat]; llia.
          * intros a Ha. pose proof (u64_range a). apply wbytes_other_Z; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat]; llia.
          * intros _. replace (Pp + nn) with (Pp + nn + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia). rewrite byte_of_0. reflexivity.
          * intros H5. llia.
        + apply Z.ltb_ge in ER5.
          eapply (ts_st_clear A HW); [exact HR4 | apply WIN_upd; exact HWIN1 | llia | intros j Hj; apply Hspan; llia
            | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat]; llia |].
          intros HR5. cbn [ms_mem ms_vm upd].
          eapply (ts_st_clear A HW); [exact HR5 | apply WIN_upd; exact HWIN1 | llia | intros j Hj; apply Hspan; llia
            | intros f Hf; destruct (Hclear f Hf); cbn [Z.of_nat Pos.to_nat]; llia |].
          intros HR6. cbn [ms_mem ms_vm upd]. apply ts_ret. split; [rewrite Z.min_r by llia; reflexivity|].
          apply BASE2; [exact HR6 | | | | |].
          * do 3 (apply rodata_clear_wbytes; [| llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; llia | rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; llia]). exact HRO3.
          * intros x Hx Hout. rewrite !mbyte_store_out by (cbn [Z.of_nat Pos.to_nat]; llia). reflexivity.
          * intros a Ha. pose proof (u64_range a). rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; llia). reflexivity.
          * intros _. destruct (Z.eq_dec RSV 5) as [E5 | N5].
            -- (* [comment removed for export] *)
               rewrite (mbyte_store_out _ (e - 4)) by (cbn [Z.of_nat Pos.to_nat]; llia).
               replace (Pp + nn) with (e - 5 + 0) by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia). rewrite byte_of_0. reflexivity.
            -- rewrite (mbyte_store_out _ (e - 4)) by (cbn [Z.of_nat Pos.to_nat]; llia).
               rewrite (mbyte_store_out _ (e - 5)) by (cbn [Z.of_nat]; llia).
               replace (Pp + nn) with (Pp + nn + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia). rewrite byte_of_0. reflexivity.
          * intros _. split.
            -- rewrite (mbyte_store_out _ (e - 4)) by (cbn [Z.of_nat Pos.to_nat]; llia).
               replace (e - 5) with (e - 5 + 0) at 2 by llia. rewrite mbyte_store_in by (cbn [Z.of_nat]; llia). rewrite byte_of_0. reflexivity.
            -- intros kk Hkk. rewrite mbyte_store_in by (cbn [Z.of_nat Pos.to_nat]; llia). rewrite uZ by llia. reflexivity. }
    intros cw s2 (-> & HI2).
    destruct HI2 as (HRb & HWINb & Hvmb & Hlob & Hhib & HROb & Hfrb & Hpayb & Hhdrb & Hbi & Hbo0 & Hbo1 & Hbz & Hbf).
    eapply (enframe_tail A s s2 ma mt aib slots i nn S Mb p0 e OFF Pp RSV OFU (Z.min RSV 5));
      try eassumption; try reflexivity; try llia.
    intros s' W' R' WIN' V' L' H' RO' FR' PAY'. apply (HK OFF s'); auto.
  Qed.
End Enframe.

End WithLayout.
