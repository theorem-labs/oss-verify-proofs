(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkShl BigLinkReduce L5Defs L5Words L5Reduce L5Shr
     L5Core L5CoreKit L5CoreKitS L5CoreSpecs L5DivSpecs L5UnnormM.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5UNNORM.
Import L5CS.
Import L5UNNM.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Ltac lastc H := repeat (lazymatch type of H with _ /\ _ => apply proj2 in H end).

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis DIVEQ : L5DS.diveq_spec L HI.
Hypothesis SHRZ : L5DS.shrz_spec L HI.
Hypothesis SHRS : L5SHR.shr_spec.
Hypothesis RED : L5RED.reduce_spec.
Let from_mid := from_mid L HI LY HIok SHRZ SHRS RED.

Theorem unnorm_ok : L5DS.unnorm_spec L HI.
Proof.
  unfold L5DS.unnorm_spec. intros fx R M model K LB cr X xs sd sp r bX wX HH MOK HK0 H11 H12 Hxs H13 Hsd H1 RA H2 H3 H4 STK IMG OB OL HLEN NEG
    Ao Olo Ohi DEFX BLK SD1 CR KONT KE3.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF).
  unfold L5DS.UNNORM_SCR, L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (DEFz: forall a, sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) <= a < sp -> M (Z_to_bv 64 a) <> None).
  { intros a Ha. replace a with (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + (a - (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224)))))))))))) by lia.
    apply DEF. lia. }
  destruct bX as [fb len sto]. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap] in HLEN, NEG, BLK, SD1, KE3.
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (WR64: BG.writable M (sp - 64) 64).
  { change (L5.writable RSEGS M (sp - 64) 64). apply (L5C.writable_of_defined RSEGS). intros i Hi. apply DEFz. lia. lia. lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8. pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9.
  pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, Hfb, O8, OST.
  pose proof OL as (Lw & Rw & Vw). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Lw, Vw.
  (* [comment removed for export] *)
  assert (DR: L5.defined M (L5.bo_data X (L5.BO fb len sto)) (8 * L5.bo_cap (L5.BO fb len sto))
              /\ (forall cap q, sto = L5.BDyn cap q -> 4096 <= q /\ q + 8 * cap <= hl_ceil L /\ Z.of_nat len <= cap)).
  { destruct sto as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st].
    - split. intros i Hi. replace (X + 16 + i) with (X + (16 + i)) by lia. apply DEFX. lia. intros; discriminate.
    - destruct (BLK cap q eq_refl) as [BLKq DEFq]. split. exact DEFq. intros c' q' E. injection E. intros <- <-.
      destruct OST as (_ & _ & _ & Hlc & Hc & _ & Qlo & _). pose proof (LBhi _ BLKq) as Hb. cbn [fst snd] in Hb. split. lia. split. lia. lia. }
  destruct DR as [DEF0 BR].
  destruct Hsd as [-> | ->].
  - (* [comment removed for export] *)
    destruct (p1n_run fx R M sp H2 H13 A16 ltac:(lia) ltac:(lia) WR64) as (fx1 & R1 & M1 & MS1 & K1 & R1_2 & R1_8 & R1_9 & C8 & C16 & C24 & FR1 & GR1).
    rewrite <- L5K.rl11, H11 in R1_8. rewrite <- L5K.rl12, H12 in R1_9.
    assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply FR1. rewrite BG.unsigned_lit by lia. exact Hna. }
    unfold L5DS.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    eapply (from_mid R M model K LB cr X xs sp r fb len sto fx1 R1 M1 model cr fb len sto wX KONT MOK HK0 H2 H1 RA H4 Hxs STK Ao Olo Ohi
              (fun cap q E => proj1 (BLK cap q E)) R1_2 R1_8 R1_9).
    + apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
    + apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
    + intros j Hj. apply (K1 j). L5K.inlist Hj.
    + exact C8. + exact C16. + exact C24.
    + eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
    + eapply (obj_limbs_agree M M1). exact OL. intros cap q E. destruct (BR cap q E) as (Q0 & Q1 & Q2). rewrite Lw.
      split. intros i Hi. apply FR1z. lia. unfold hl_ceil in Q1. lia. split. lia. unfold hl_ceil in Q1. lia.
    + exact NEG.
    + lia.
    + destruct sto; cbn; auto.
    + left. lia.
    + intros i Hi. apply GR1. apply DEF0. exact Hi.
    + intros i Hi. apply GR1. apply DEFX. exact Hi.
    + (* [comment removed for export] *)
      unfold L5DS.UNNORM_SCR, L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
      split. { intros a Ka. pose proof Ka as (Ha & _).
               pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
               apply FR1z. lia. intros HC; apply NS; lia. }
      split. { intros i Hi. apply GR1. apply DEF. exact Hi. }
      intros a Ha CA NE D0. apply GR1. exact D0.
    + eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hlt|Hge]. left. apply FR1z; lia.
      destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. unfold hl_ceil. lia. left. apply FR1z; lia. exact GR1.
    + apply L5C.model_but_vm_refl.
    + unfold L5DS.credit_after, L5DS.DIVN_K, L5DS.DIVN_BYTES. split; lia.
  - (* [comment removed for export] *)
    destruct (SD1 eq_refl) as (qX & HST & HLEN2). subst sto. specialize (CR eq_refl).
    destruct OST as (B0 & O16 & O24 & Hlc & Hcap & Aq & Qlo & Qhi & HAP).
    destruct (BLK 8 qX eq_refl) as [BLKq DEFQ]. destruct (BR 8 qX eq_refl) as (_ & QXhi & _).
    destruct (p1s_run fx R M sp H2 H13 A16 ltac:(lia) ltac:(lia) WR64)
      as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & C8 & C16 & C24 & T56 & T48 & T40 & T32 & FR1 & GR1).
    rewrite <- L5K.rl11, H11 in R1_8, R1_10. rewrite <- L5K.rl12, H12 in R1_9.
    assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply FR1. rewrite BG.unsigned_lit by lia. exact Hna. }
    assert (MW1: L5DS.mword_obj M1 (sp - 56) 0).
    { unfold L5DS.mword_obj, L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st Z.of_nat Pos.to_nat]. split. 2: reflexivity.
      split. exact T56. split. lia. split. replace (sp - 56 + 8) with (sp - 48) by lia. exact T48. split. reflexivity.
      split. replace (sp - 56 + 16) with (sp - 40) by lia. unfold L5DS.MWORD. exact T40. split. replace (sp - 56 + 24) with (sp - 32) by lia. exact T32.
      split. lia. unfold L5DS.MWORD. lia. }
    unfold L5DS.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
    eapply (DIVEQ fx1 R1 M1 model K LB cr X qX (sp - 56) 0 (sp - 64) DIVEQ_RET (L5.BO fb len (L5.BDyn 8 qX)) wX).
    + eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
      intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hlt|Hge]. left. apply FR1z; lia.
      destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. unfold hl_ceil. lia. left. apply FR1z; lia. exact GR1.
    + exact MOK.
    + exact HK0.
    + exact R1_10.
    + exact R1_11.
    + exact R1_1.
    + split. unfold DIVEQ_RET. lia. reflexivity.
    + exact R1_2.
    + rewrite <- H3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
    + rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
    + split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
      unfold L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
      intros i Hi. apply GR1. apply DEFz. lia.
    + intros i Hi. rewrite FR1z by lia. apply IMG. exact Hi.
    + eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
    + eapply (obj_limbs_agree M M1). exact OL. intros cap q E. injection E. intros <- <-. rewrite Lw.
      split. intros i Hi. apply FR1z. lia. unfold hl_ceil in QXhi. lia. split. lia. unfold hl_ceil in QXhi. lia.
    + reflexivity.
    + exact HLEN2.
    + exact NEG.
    + exact BLKq.
    + intros i Hi. apply GR1. apply DEFQ. lia.
    + exact Ao.
    + lia.
    + exact Ohi.
    + intros i Hi. apply GR1. apply DEFX. exact Hi.
    + exact MW1.
    + assert (A8: sp mod 8 = 0). { apply Z.mod_divide. lia. apply Z.mod_divide in A16. 2: lia. destruct A16 as [c Hc]. exists (2 * c). lia. }
      replace (sp - 56) with (sp + (-7) * 8) by lia. rewrite Z_mod_plus_full. exact A8.
    + lia.
    + lia.
    + right. lia.
    + exact CR.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 cr2 POST2 MBV2 HH2.
      destruct POST2 as (RP2 & R2_10 & (fbq & nq & wq & OBX & OLX & NEGq & Hnq & DEFq) & MW2 & CRA2 & HP2).
      destruct HP2 as (PRES2 & SDEF2 & CDEF2).
      unfold L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES2, SDEF2, CDEF2.
      pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
      assert (CL2: forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. apply PRES2. apply (L5C.kept_stack L LB (sp - 64) _ _). lia. lia. lia. rewrite (ly_errno L LY). lia. lia.
        apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. lia.
        apply L5C.outside_cons. unfold L5.in_rng. cbn [fst snd]. unfold hl_ceil in QXhi. lia. apply L5C.outside_nil. }
      assert (T2: forall a v, sp - 64 <= a -> a + 8 <= sp -> BG.u64_at M1 a v -> BG.u64_at M2 a v).
      { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact Hu. }
      destruct MW2 as [[U56 _] _]. cbn [L5.bo_fb] in U56.
      assert (WR2: BG.writable M2 (sp - 64) 64).
      { change (L5.writable RSEGS M2 (sp - 64) 64). apply (L5C.writable_of_defined RSEGS). 2: lia. 2: lia.
        intros i Hi. rewrite CL2 by lia. apply GR1. apply DEFz. lia. }
      assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite <- L5K.rl2, (RP2 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R1_2. }
      assert (R2_8: getr R2 (reg 8) = Z_to_bv 64 X). { rewrite <- L5K.rl8, (RP2 8%bv ltac:(cbn; tauto)), L5K.rl8. exact R1_8. }
      assert (R2_9: getr R2 (reg 9) = Z_to_bv 64 xs). { rewrite <- L5K.rl9, (RP2 9%bv ltac:(cbn; tauto)), L5K.rl9. exact R1_9. }
      destruct (p2_run fx2 R2 M2 X xs sp R2_2 R2_8 R2_9 ltac:(lia) ltac:(lia) U56 A16 ltac:(lia) ltac:(lia) WR2)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_2 & R3_8 & R3_9 & MF3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      eapply (from_mid R M model K LB cr X xs sp r fb len (L5.BDyn 8 qX) fx3 R3 M3 model2 cr2 fbq nq (L5.BDyn 8 qX) wq KONT MOK HK0 H2 H1 RA H4 Hxs STK Ao Olo Ohi
                (fun cap q E => proj1 (BLK cap q E)) R3_2 R3_8 R3_9).
      * rewrite (K3 3%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl3, (RP2 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
      * rewrite (K3 4%nat) by (apply L5K.In_of_mem; reflexivity). rewrite <- L5K.rl4, (RP2 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
      * intros j Hj. assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H'). assert (M3j: In j KS2) by (pose proof Hj as H'; L5K.inlist H').
        assert (M1j: In j KS1S) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M3j). rewrite (L5K.regs_preserved_index R1 R2 j RP2 MCj). apply (K1 j M1j).
      * eapply (L5C.u64_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. apply T2. lia. lia. exact C8.
      * eapply (L5C.u64_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. apply T2. lia. lia. exact C16.
      * eapply (L5C.u64_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. apply T2. lia. lia. exact C24.
      * eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply MF3. lia. lia. exact OBX.
      * eapply (obj_limbs_agree M2 M3). exact OLX. intros cap q E. injection E. intros <- <-. destruct OLX as (Lq & _). cbn [L5.bo_len] in Lq. rewrite Lq.
        split. intros i Hi. apply MF3. split. lia. unfold hl_ceil in QXhi. lia.
      * exact NEGq.
      * lia.
      * cbn. split; reflexivity.
      * right. exists 8, qX. reflexivity.
      * cbn [L5.bo_data L5.bo_cap L5.bo_st]. intros i Hi. rewrite (MF3 (Z_to_bv 64 _)). apply DEFq. lia.
      * intros i Hi. rewrite (MF3 (Z_to_bv 64 _)). apply (CDEF2 (X + i)). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia.
        apply GR1. apply DEFX. exact Hi.
      * (* [comment removed for export] *)
        unfold L5DS.UNNORM_SCR, L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. cbn [L5.bo_data L5.bo_cap L5.bo_st Z.mul].
        split.
        { intros a Ka. pose proof Ka as (Ha & _).
          pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
          rewrite (MF3 (Z_to_bv 64 a)). rewrite (PRES2 a). apply FR1z. lia. intros HC; apply NS; lia.
          eapply L5C.kept_inner. exact Ka. lia. lia. intros OW. exact OW. }
        split.
        { intros i Hi. rewrite (MF3 (Z_to_bv 64 _)).
          destruct (Z_lt_le_dec (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + i) (sp - 64)) as [Hlt|Hge].
          -- replace (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + i)
               with (sp - 64 - (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224)))))))) + i) by lia. apply SDEF2. lia.
          -- apply (CDEF2 _). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
        intros a Ha CA NE D0. rewrite (MF3 (Z_to_bv 64 a)). apply (CDEF2 a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact D0.
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. left. apply MF3. exact GR3.
      * exact MBV2.
      * exact CRA2.
    + (* [comment removed for export] *)
      intros fx2 R2 M2 model2 LB' cr' E3 MBV2 HH2.
      apply (KE3 fx2 R2 M2 model2 qX LB' cr' eq_refl eq_refl). 2: exact MBV2. 2: exact HH2.
      pose proof E3 as E3'. destruct E3' as (RN & MN & HX). lastc HX. destruct HX as (PRES2 & SDEF2 & CDEF2).
      unfold L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES2, SDEF2, CDEF2.
      assert (CL2: forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. apply PRES2. apply (L5C.kept_stack L LB (sp - 64) _ []). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. apply L5C.outside_nil. }
      exists R1, M1.
      split. exact R1_1. split. exact R1_2. split. exact R1_8. split. rewrite H12. exact R1_9.
      split. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity.
      split. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity.
      split. { apply sregs_cases. intros j Hj. apply (K1 j). L5K.inlist Hj. }
      split. exact E3.
      unfold L5DS.U.
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact C8. }
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact C16. }
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact C24. }
      split. { eapply (L5C.u8_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact T56. }
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact T48. }
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. unfold L5DS.MWORD. exact T40. }
      split. { eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL2. lia. lia. lia. exact T32. }
      unfold L5DS.UNNORM_SCR, L5DS.DIVEQ_SCR, L5DS.DIV_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK.
      split.
      { intros a Ka. pose proof Ka as (Ha & _).
        pose proof (kept_not_scratch L LB sp _ _ a Ka LBhi ltac:(unfold hl_ceil; lia) ltac:(rewrite (ly_img_hi L LY); lia)) as NS.
        rewrite (PRES2 a). apply FR1z. lia. intros HC; apply NS; lia. eapply L5C.kept_inner. exact Ka. lia. lia. intros _. apply L5C.outside_nil. }
      split.
      { intros i Hi.
        destruct (Z_lt_le_dec (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + i) (sp - 64)) as [Hlt|Hge].
        -- replace (sp - (64 + (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224))))))))) + i)
             with (sp - 64 - (48 + (304 + (64 + (48 + (64 + (64 + (64 + (16 + 8224)))))))) + i) by lia. apply SDEF2. lia.
        -- apply (CDEF2 _). lia. right. left. unfold hl_ceil. lia. unfold in_errno. rewrite (ly_errno L LY). lia. apply GR1. apply DEFz. lia. }
      intros a Ha CA NE D0. apply (CDEF2 a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact D0.
Qed.

End WithHeap.
End SCFG_1.
End L5UNNORM.
