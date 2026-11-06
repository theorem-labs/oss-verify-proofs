(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanPlanSoundSums Ub0Sums
     BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU L5ResizeU L5AssignPU L5AssignTU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASGU.
Import L5CSU.
Import L5ASGPU.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Lemma assign_fb_eq fb fb' (n : nat) (grown : bool) : (1 <= n)%nat ->
  assign_fb fb fb' n grown = assign_flags (if grown then Z.lor fb 1 else fb) fb'.
Proof. intros Hn. unfold assign_fb, assign_flags. destruct n. lia. cbn [Nat.eqb]. apply Z.lor_comm. Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem assign_ok : assign_spec L HI.
Proof.
  unfold assign_spec. intros fx R M model K LB cr o o' sp r b b' ws' HH MOK HK0 H10 H11 Hn CAP CR H1 RA H2 H4 STK OB Ao Olo Ohi WO BLK OB' OL' Ao' Olo' Ohi' BLK' APO APQ KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (LBwf: forall q c, In (q, 8 * c) LB -> (4096 <= q /\ (q + 8 * c <= 0x10000 \/ 0x92000 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M q (8 * c)).
  { intros q c Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4) & QD & _). cbn [fst snd] in Q0, Q1, Q4, QD.
    rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. split. split. exact Q0. exact Q1. split. exact Q4. exact QD. }
  assert (WR48: BGU.writable M (sp - 48) 48).
  { change (L5.writable RSEGS M (sp - 48) 48). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). destruct b' as [fb' len' sto']. pose proof OB' as (O0' & Hfb' & O8' & OST').
  cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  destruct OL' as (Lws' & Rws' & Vws'). cbn [L5.bo_len L5.bo_st] in Lws', Vws'.
  (* [comment removed for export] *)
  assert (Y24: exists y24, BGU.u64_at M (o' + 24) y24 /\ 0 <= y24 < 2 ^ 64 /\ match sto' with L5.BInl _ v1 => y24 = v1 | L5.BDyn _ q' => y24 = q' end).
  { destruct sto' as [v0' v1'|cap' q']. destruct OST' as (_ & _ & O24' & _ & _ & R1). exists v1'. repeat split; try lia. exact O24'.
    destruct OST' as (_ & _ & O24' & _ & Hc' & _ & Qlo & Qhi). exists q'. repeat split; try lia. exact O24'. }
  destruct Y24 as (y24 & O24' & Hy24 & Ey24).
  (* [comment removed for export] *)
  assert (WST: exists wsT, L5C.obj_limbs RSEGS M (L5.BO fb len sto) wsT).
  { destruct sto as [v0 v1|cap q].
    - exists (firstn len [v0; v1]). destruct OST as (_ & _ & _ & Hl2 & R0 & R1). split. cbn. rewrite length_firstn. cbn. lia.
      split. cbn. destruct len as [|[|[|k]]]; cbn; repeat constructor; lia. reflexivity.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Aq & Qlo & Qhi). destruct (LBwf q cap (BLK cap q eq_refl)) as (QR & QB & QD).
      destruct (L5KU.limbs_of_defined M q len ltac:(eapply L5.defined_sub; [exact QD|lia|lia]) ltac:(lia) ltac:(lia)) as (ws & L1 & R1 & LA).
      exists ws. split. cbn. exact L1. split. exact R1. cbn. exact LA. }
  destruct WST as (wsT & OLT).
  assert (Hlen: Z.of_nat len <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. destruct OST as (_ & _ & _ & Hl2 & _). lia. destruct OST as (_ & _ & _ & Hlc & Hc & _). lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
  pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
  pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as RG19. pose proof (bv_unsigned_in_range _ (getr R (reg 20))) as RG20.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18, RG19, RG20.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  assert (NEQ: o <> o') by lia.
  (* [comment removed for export] *)
  set (od := L5.bo_dyn (L5.BO fb' len' sto')). set (src := L5.bo_data o' (L5.BO fb' len' sto')).
  assert (BtO: Z.testbit fb' 0 = od). { subst od. reflexivity. }
  assert (Esrc: (if od then y24 else o' + 16) = src).
  { subst od src. unfold L5.bo_dyn. cbn [L5.bo_fb L5.bo_data L5.bo_st]. destruct sto' as [w0 w1|c q]; destruct OST' as (B & _); rewrite B; [reflexivity|]. exact Ey24. }
  assert (SRCG: 4096 <= src < 2 ^ 47 /\ src mod 8 = 0 /\ src + 8 * Z.of_nat len' <= 2 ^ 47).
  { subst src. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st].
    - destruct OST' as (_ & _ & _ & Hl2' & _). split. lia. split. rewrite <- Z.add_mod_idemp_l by lia. rewrite Ao'. reflexivity. lia.
    - destruct OST' as (B1' & O16' & O24x & Hlc' & Hc' & Aq' & Qlo' & Qhi'). destruct (LBwf q' c' (BLK' c' q' eq_refl)) as (X1 & X2 & X3). split. lia. split. exact Aq'. lia. }
  destruct SRCG as (SRCr & SRCa & SRCe).
  destruct (p1_run od fx R M o o' sp fb' (Z.of_nat len') y24 H10 H11 NEQ ltac:(lia) ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR48 Ao' Olo' ltac:(lia)
              O0' Hfb' BtO O8' ltac:(lia) O24' Hy24)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_18 & R1_19 & C8 & C16 & C24 & C32 & C40 & FR1 & GR1).
  rewrite Esrc in R1_9.
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 48 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BGU.unsigned_lit by lia. exact Hna. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (L5RSZU.resize_ok L HI LY HIok fx1 R1 M1 model K LB cr o (sp - 48) RET1 len' (L5.BO fb len sto) wsT).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 48)) as [Hlt|Hge]. left. apply FR1z; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1z; lia. exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - exact R1_11.
  - lia.
  - exact CAP.
  - exact CR.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 48 - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - (48 + (64 + (48 + (64 + (16 + 8224))))) + i) by lia. apply DEF. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
  - (* [comment removed for export] *)
    destruct OLT as (LT & RT & VT). split. exact LT. split. exact RT. cbn [L5.bo_st L5.bo_len] in VT |- *.
    destruct sto as [v0 v1|cap q]. exact VT.
    destruct (LBwf q cap (BLK cap q eq_refl)) as (QR & QB & QD). cbn in LT.
    eapply (L5C.limbs_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact VT.
  - exact Ao.
  - lia.
  - exact Ohi.
  - change (L5.writable RSEGS M1 o 32). eapply L5.writable_grows. exact GR1. exact WO.
  - exact BLK.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB' cr' POST MBV HH2.
    pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
    destruct POST as [RP POST].
    (* [comment removed for export] *)
    assert (SIT: exists (fbR : Z) (stR : L5.bstore) (grown : bool) (W2 : list L5.range),
              L5.big_at RSEGS M2 o (L5.BO fbR len' stR) /\ fbR = (if grown then Z.lor fb 1 else fb) /\ Z.testbit fbR 0 = (grown || Z.testbit fb 0)%bool
              /\ L5C.hpres L LB (sp - 48) RESIZE_SCR ((o, 32) :: W2) M1 M2
              /\ (forall a rg, In rg W2 -> L5.in_rng rg a -> L5.bo_data o (L5.BO fb len sto) <= a < L5.bo_data o (L5.BO fb len sto) + 8 * Z.max (Z.of_nat len') (Z.of_nat len) /\ grown = false)
              /\ L5.defined M2 (L5.bo_data o (L5.BO fbR len' stR)) (8 * Z.of_nat len')
              /\ L5.bo_data o (L5.BO fbR len' stR) + 8 * Z.of_nat len' <= 2 ^ 47 /\ 4096 <= L5.bo_data o (L5.BO fbR len' stR)
              /\ match g with
                 | Same => grown = false /\ LB' = LB /\ cr' = cr /\ (L5.bo_dyn (L5.BO fb len sto) = true \/ (len' <= 2)%nat)
                           /\ match sto, stR with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => (len' <= 2)%nat | _, _ => False end
                 | Grown A cap => grown = true /\ stR = L5.BDyn cap A /\ (3 <= len')%nat /\ cap = round_up (Z.of_nat len') /\ LB' = (A, 8 * cap) :: LB
                           /\ cr' = debit L cr (8 * cap) /\ L5C.fresh_block L LB M2 A (8 * cap) /\ Z.testbit fb 0 = false
                 end).
    { destruct g as [|A cap].
      - destruct POST as (HG & HLB & HCR & (stR & OBR & OLR & MATCH) & HP). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OBR, OLR, MATCH, HP.
        exists fb, stR, false, [(L5.bo_data o (L5.BO fb len sto) + 8 * Z.of_nat len, 8 * Z.max 0 (Z.of_nat len' - Z.of_nat len))].
        split. exact OBR. split. reflexivity. split. reflexivity. split. exact HP.
        split. { intros a rg [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [|reflexivity]. cbn [L5.bo_data L5.bo_st]. lia. }
        destruct OLR as (LR & RR & VR). cbn [L5.bo_len L5.bo_st] in LR, VR.
        destruct stR as [w0 w1|capR qR]; destruct sto as [v0 v1|cap q]; try contradiction.
        + destruct OBR as (_ & _ & _ & _ & Q16 & Q24 & Hl2 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Hl2. cbn [L5.bo_data L5.bo_st].
          split. { replace (8 * Z.of_nat len') with (8 + (8 * Z.of_nat len' - 8)) by lia. apply (L5C.defined_app M2 (o + 16) 8 (8 * Z.of_nat len' - 8)); [| |lia].
                   eapply L5KU.u64_at_defined. exact Q16. unfold L5KU.IMG_HI; lia. lia.
                   destruct (Z_lt_le_dec 8 (8 * Z.of_nat len')); [| intros i Hi; lia].
                   eapply (L5.defined_sub M2 (o + 24) 8). eapply L5KU.u64_at_defined. exact Q24. unfold L5KU.IMG_HI; lia. lia. lia. lia. }
          split. lia. split. lia. split. reflexivity. split. exact HLB. split. exact HCR. split. exact HG. exact Hl2.
        + destruct MATCH as [-> ->]. destruct OBR as (_ & _ & _ & _ & Q16 & Q24 & Hlc & Hc & Aq & Qlo & Qhi & HAPq). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Hlc. cbn [L5.bo_data L5.bo_st].
          destruct (LBwf q cap (BLK cap q eq_refl)) as (QR & QB & QD).
          split. { pose proof (L5KU.limbs_at_defined_hull M2 q _ VR ltac:(lia) ltac:(rewrite L5RSZU.resize_limbs_length; eapply L5.hull_apart_sub; [exact HAPq|lia|lia]) ltac:(rewrite L5RSZU.resize_limbs_length; lia)) as D.
                   rewrite L5RSZU.resize_limbs_length in D. exact D. }
          split. lia. split. lia. split. reflexivity. split. exact HLB. split. exact HCR. split. exact HG. split; reflexivity.
      - destruct POST as (B0 & H3 & Hcap & HLB' & Hcr' & FB & OBR & OLR & HP). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_data] in OBR, OLR, HP.
        exists (Z.lor fb 1), (L5.BDyn cap A), true, []. pose proof FB as ((BR0 & BR1 & BR2 & BR3 & BR4) & BA & DEFA).
        rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1. pose proof (L5ARESU.round_up_bounds (Z.of_nat len') ltac:(lia)) as [RB RM].
        split. exact OBR. split. reflexivity. split. { cbn. apply L5RESU.lor1_bit0. } split. exact HP.
        split. { intros a rg []. }
        cbn [L5.bo_data L5.bo_st]. split. { eapply L5.defined_sub. exact DEFA. lia. lia. } split. lia. split. lia. split. reflexivity. split. reflexivity.
        split. exact H3. split. exact Hcap. split. exact HLB'. split. exact Hcr'. split. exact FB. unfold L5.bo_dyn in B0. cbn [L5.bo_fb] in B0. exact B0. }
    destruct SIT as (fbR & stR & grown & W2 & OBR & EfbR & BfbR & HP & HW2 & DDST & DSThi & DSTlo & GCASE).
    set (dst := L5.bo_data o (L5.BO fbR len' stR)) in *.
    pose proof OBR as (Q0 & HfbR & Q8 & QST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Q0, HfbR, Q8, QST.
    pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP) as SDEF. pose proof (fun a => L5C.hpres_cdef _ _ _ _ _ _ _ a HP) as CDEF. cbn beta in CDEF.
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SDEF, CDEF.
    assert (DHI: forall a, grown = false -> L5.bo_data o (L5.BO fb len sto) <= a < L5.bo_data o (L5.BO fb len sto) + 8 * Z.max (Z.of_nat len') (Z.of_nat len) ->
                 a < hl_ceil L \/ o + 16 <= a < o + 32).
    { intros a G0 Ha. destruct sto as [v0 v1|cap q].
      - right. destruct OST as (B1 & _ & _ & Hl2 & _). cbn [L5.bo_data L5.bo_st] in Ha.
        assert (len' <= 2)%nat. { destruct g. destruct GCASE as (_ & _ & _ & HG & _). destruct HG as [Hd|Hl]. unfold L5.bo_dyn in Hd. cbn [L5.bo_fb] in Hd. rewrite B1 in Hd. discriminate. exact Hl.
                                  destruct GCASE as (G1 & _). rewrite G0 in G1. discriminate. }
        lia.
      - left. destruct OST as (B1 & _ & _ & Hlc & _). destruct (LBwf q cap (BLK cap q eq_refl)) as (QR & QB & QD).
        cbn [L5.bo_data L5.bo_st] in Ha. specialize (CAP B1). cbn in CAP. lia. }
    assert (CL: forall a, sp - 48 <= a < 2 ^ 47 -> ~ (o <= a < o + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply (L5C.kept_stack L LB (sp - 48) _ ((o, 32) :: W2)). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. lia.
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia. lia. rewrite (ly_errno L LY). lia. lia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. intros rg Hrg Hin. destruct (HW2 a rg Hrg Hin) as [X G0].
      destruct (DHI a G0 X); lia. }
    assert (T1: forall a v, sp - 48 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia. exact Hu. }
    assert (WR2 : BGU.writable M2 (sp - 48) 48).
    { change (L5.writable RSEGS M2 (sp - 48) 48). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WR48. }
    assert (AT: at_ret1 R2 M2 o src (Z.of_nat len') o' sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                  (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19)))).
    { unfold at_ret1.
      split. { rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8. exact R1_8. }
      split. { rewrite <- L5K.rl9, (RP 9%bv ltac:(cbn; tauto)), L5K.rl9. exact R1_9. }
      split. { rewrite <- L5K.rl18, (RP 18%bv ltac:(cbn; tauto)), L5K.rl18. exact R1_18. }
      split. { rewrite <- L5K.rl19, (RP 19%bv ltac:(cbn; tauto)), L5K.rl19. exact R1_19. }
      split. { rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R1_2. }
      split. apply T1; [lia|lia|exact C8]. split. apply T1; [lia|lia|exact C16]. split. apply T1; [lia|lia|exact C24].
      split. apply T1; [lia|lia|exact C32]. split. apply T1; [lia|lia|exact C40]. lia. }
    (* [comment removed for export] *)
    assert (KEEP: forall a, L5C.kept L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) ((o, 32) :: match g with Same => [(L5.bo_data o (L5.BO fb len sto), 8 * Z.max (Z.of_nat len') (Z.of_nat len))] | Grown _ _ => [] end) a ->
                    M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a KA. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
      rewrite (L5C.hpres_kept _ _ _ _ _ _ _ a HP). apply FR1z. lia.
      { destruct CA as [IB|[[S1 S2]|IM]]. destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). lia. lia. rewrite (ly_img_hi L LY) in IM. lia. }
      eapply L5C.kept_inner. exact KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia. lia.
      intros _. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. intros rg Hrg Hin. destruct (HW2 a rg Hrg Hin) as [X G0].
      destruct g. apply L5C.outside_cons_inv in OW2 as [NW2 _]. unfold L5.in_rng in NW2. cbn [fst snd] in NW2. lia. destruct GCASE as (G1 & _). rewrite G0 in G1. discriminate. }
    assert (CD2: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (48 + (64 + (48 + (64 + (16 + 8224))))) a -> ~ in_errno L a ->
                 M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
    { intros a Ha CA NE DM. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact DM. }
    assert (REGS: forall (R3 : bvmap 5 word) (ks : list nat),
              (forall x, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat ks ->
              getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) ->
              getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) ->
              getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19))) ->
              regs_preserved R R3).
    { intros R3 ks K3 Hincl S2 S8 S9 S18 S19. apply L5K.regs_preserved_by_index. intros i Hi.
      cbn in Hi. destruct Hi as [<-|Hi]. { rewrite S2, <- H2, L5K.rl2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S9. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S18. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S19. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      assert (G: forall j, In j [20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
      { intros j Hj.
        assert (M2j: In j ks) by (apply Hincl; cbn in Hj |- *; tauto).
        assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
        assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
      apply G. L5K.inlist Hi. }
    (* [comment removed for export] *)
    assert (SDEF_of: forall M5 : word -> option byte, (forall a, sp - (48 + (64 + (48 + (64 + (16 + 8224))))) <= a < sp -> M5 (Z_to_bv 64 a) <> None \/ M5 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) ->
                     mem_grows M2 M5 -> L5.defined M5 (sp - (48 + (64 + (48 + (64 + (16 + 8224)))))) (48 + (64 + (48 + (64 + (16 + 8224)))))).
    { intros M5 HM GR i Hi. apply GR.
      destruct (Z_lt_le_dec (sp - (48 + (64 + (48 + (64 + (16 + 8224))))) + i) (sp - 48)) as [Hlt|Hge].
      - replace (sp - (48 + (64 + (48 + (64 + (16 + 8224))))) + i) with (sp - 48 - (64 + (48 + (64 + (16 + 8224)))) + i) by lia. apply SDEF. lia.
      - rewrite CL by lia. apply GR1. apply DEF. lia. }
    (* [comment removed for export] *)
    set (td := match stR with L5.BDyn _ _ => true | L5.BInl _ _ => false end).
    assert (BtR: Z.testbit fbR 0 = td). { subst td. destruct stR; destruct QST as (B & _); exact B. }
    assert (Q24: td = true -> BGU.u64_at M2 (o + 24) dst).
    { subst td dst. destruct stR as [w0 w1|c q]. discriminate. intros _. destruct QST as (_ & _ & Q24 & _). exact Q24. }
    assert (Edst: (if td then dst else o + 16) = dst). { subst td dst. destruct stR; reflexivity. }
    assert (DSTG: 4096 <= dst < 2 ^ 47 /\ dst mod 8 = 0).
    { subst dst. destruct stR as [u0 u1|cR qR]; cbn [L5.bo_data L5.bo_st].
      - split. lia. rewrite <- Z.add_mod_idemp_l by lia. rewrite Ao. reflexivity.
      - destruct QST as (_ & _ & _ & HlcR & HcR & AqR & QloR & QhiR). split. lia. exact AqR. }
    destruct DSTG as (DSTr & DSTa).
    destruct (Nat.eq_dec len' 0) as [LEN0|LENP].
    + (* [comment removed for export] *)
      assert (LZ: Z.of_nat len' = 0) by lia.
      assert (AT0: at_ret1 R2 M2 o src 0 o' sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9)))
                    (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19)))). { rewrite <- LZ. exact AT. }
      destruct (epilogue_z_run td fx2 R2 M2 o src o' sp _ _ _ _ _ r fbR dst AT0
                  ltac:(lia) ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo ltac:(lia) Q0 HfbR BtR Q24 ltac:(lia) E1 RA)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_19 & R3_10 & MM3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      assert (OB3: L5.big_at RSEGS M3 o (L5.BO fbR len' stR)). { eapply (L5C.big_at_agree RSEGS M2 M3). intros i Hi. apply MM3. lia. lia. exact OBR. }
      assert (OL3: L5C.obj_limbs RSEGS M3 (L5.BO fbR len' stR) ws').
      { split. cbn. lia. split. exact Rws'. destruct ws'; [|cbn in Lws'; lia]. cbn [L5.bo_st L5.bo_len]. destruct stR. rewrite LEN0. reflexivity. apply L5C.limbs_at_nil. }
      assert (FB0: assign_fb fb fb' len' grown = fbR). { unfold assign_fb. rewrite LEN0. cbn [Nat.eqb]. symmetry. exact EfbR. }
      apply (KONT fx3 R3 M3 model2 g LB' cr').
      * split. { apply (REGS R3 KSZ K3). intros x Hx. L5K.inlist Hx. exact R3_2. exact R3_8. exact R3_9. exact R3_18. exact R3_19. }
        split. exact R3_10. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data].
        destruct g as [|A cap].
        -- destruct GCASE as (G0 & -> & -> & HG & MATCH). subst grown. rewrite FB0.
           split. exact HG. split. reflexivity. split. reflexivity.
           split. { exists stR. split. exact OB3. split. exact OL3. destruct sto; destruct stR; try exact MATCH. exact I. }
           split.
           ++ intros a KA. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA. rewrite (MM3 (Z_to_bv 64 a)). apply KEEP. exact KA.
           ++ split. { unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. apply SDEF_of. intros a Ha. right. apply MM3. exact GR3. }
              intros a Ha CA NE DM. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR3. apply CD2; assumption.
        -- destruct GCASE as (G1 & -> & H3 & _). lia.
      * exact MBV.
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. left. apply MM3. exact GR3.
    + (* [comment removed for export] *)
      apply (L5ASGTU.assign_tail L HI LY HIok fx R M model K LB cr o o' sp r fb len sto fb' len' sto' ws' Hn CAP CR RA Ao Olo Ohi BLK Lws' Rws' Vws' Ao' Olo' Ohi' BLK' APO APQ KONT A16 SLO SHI STOP Hr He LBhi LBwf Hfb OST O0' Hfb' OST' y24 Hy24 Ey24 wsT Hlen RG1 RG8 RG9 RG18 RG19 RG20 E1 NEQ BtO Esrc SRCr SRCa SRCe M1 fx2 R2 M2 model2 g LB' cr' POST MBV HH2 Mh2 Ml2 fbR stR grown EfbR BfbR DDST DSThi DSTlo GCASE Q0 HfbR Q8 QST DHI WR2 AT KEEP CD2 REGS SDEF_of BtR Q24 Edst DSTr DSTa LENP).
Qed.

End WithHeap.
End SCFG_1.

End L5ASGU.
