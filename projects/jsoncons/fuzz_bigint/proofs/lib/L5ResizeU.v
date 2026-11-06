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
     BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU L5Defs L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5RSZU.
Import L5CSU.
Import L5RSZPU.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Lemma resize_limbs_short ws n : (n <= length ws)%nat -> resize_limbs ws n = firstn n ws.
Proof. intros H. unfold resize_limbs. replace (n - length ws)%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma resize_limbs_long ws n : (length ws <= n)%nat -> resize_limbs ws n = ws ++ repeat 0 (n - length ws).
Proof. intros H. unfold resize_limbs. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma resize_limbs_length ws n : length (resize_limbs ws n) = n.
Proof. unfold resize_limbs. rewrite length_app, length_firstn, repeat_length. lia. Qed.
Lemma in_firstn {A} (x : A) : forall (l : list A) n, In x (firstn n l) -> In x l.
Proof. induction l as [|y l IH]; intros [|n] Hx; cbn in Hx; try tauto. destruct Hx as [Hx|Hx]. left; exact Hx. right. exact (IH n Hx). Qed.
Lemma resize_limbs_range ws n : Forall (fun w => 0 <= w < 2 ^ 64) ws -> Forall (fun w => 0 <= w < 2 ^ 64) (resize_limbs ws n).
Proof.
  intros H. unfold resize_limbs. apply Forall_app. split.
  - rewrite Forall_forall in H |- *. intros x Hx. apply H. exact (in_firstn x ws n Hx).
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. lia.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem resize_ok : resize_spec L HI.
Proof.
  unfold resize_spec. intros fx R M model K LB cr o sp r n b ws HH MOK HK0 H10 H11 Hn CAP CR H1 RA H2 H4 STK OB OL Ao Olo Ohi WO BLK KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (WR64: BGU.writable M (sp - 64) 64).
  { change (L5.writable RSEGS M (sp - 64) 64). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  destruct OL as (Lws & Rws & Vws). cbn [L5.bo_len L5.bo_st] in Lws, Vws.
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
  pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  assert (Hlen: Z.of_nat len <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. destruct OST as (_ & _ & _ & Hl2 & _). lia. destruct OST as (_ & _ & _ & Hlc & Hc & _). lia. }
  destruct (p1_run fx R M o (Z.of_nat n) sp (Z.of_nat len) H10 ltac:(lia) H11 ltac:(lia) H2 A16 ltac:(lia) ltac:(lia) WR64 Ao Olo ltac:(lia) O8 ltac:(lia))
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & R1_18 & C8 & C16 & C24 & C32 & FR1 & GR1).
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BGU.unsigned_lit by lia. exact Hna. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (L5RESU.reserve_ok L HI LY HIok fx1 R1 M1 model K LB cr o (Z.of_nat n) (sp - 64) RET1 (L5.BO fb len sto)).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [Hlt|Hge]. left. apply FR1z; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1z; lia. exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - exact R1_11.
  - lia.
  - exact CAP.
  - intros B0 H3. apply CR. lia. exact B0.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 64 - (48 + (64 + (16 + 8224))) + i) with (sp - (64 + (48 + (64 + (16 + 8224)))) + i) by lia. apply DEF. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
  - exact Ao.
  - lia.
  - exact Ohi.
  - change (L5.writable RSEGS M1 o 32). eapply L5.writable_grows. exact GR1. exact WO.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB' cr' POST MBV HH2.
    pose proof (L5C.halted_but_vm _ _ MBV) as Mh2. rewrite Mh in Mh2. pose proof (L5C.lazy_but_vm _ _ MBV) as Ml2. rewrite Ml in Ml2.
    destruct POST as [RP POST].
    (* [comment removed for export] *)
    assert (HPc: exists W, L5C.hpres L LB (sp - 64) RESERVE_SCR W M1 M2 /\ forall a, L5.outside W a \/ (o <= a < o + 32)).
    { destruct g as [|A cap].
      - destruct POST as (_ & _ & _ & _ & HP). exists []. split. exact HP. intros a. left. apply L5C.outside_nil.
      - destruct POST as (_ & _ & _ & _ & _ & _ & _ & _ & HP). exists [(o, 32)]. split. exact HP.
        intros a. destruct (Z_lt_le_dec a o) as [X|X]. left. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil.
        destruct (Z_lt_le_dec a (o + 32)) as [Y|Y]. right; lia. left. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
    destruct HPc as (W & (PRES & SDEF & CDEF) & HW). unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in PRES, SDEF, CDEF.
    assert (CD2: forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (64 + (48 + (64 + (16 + 8224)))) a -> ~ in_errno L a ->
                 M (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
    { intros a Ha CA NE DM. apply (CDEF a Ha). eapply L5K.client_inner. exact CA. lia. lia. exact NE. apply GR1. exact DM. }
    assert (CL: forall a, sp - 64 <= a < 2 ^ 47 -> ~ (o <= a < o + 32) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply PRES. destruct (HW a) as [HWa|HWa]; [|exfalso; lia].
      apply (L5C.kept_stack L LB (sp - 64) (48 + (64 + (16 + 8224))) W). lia. lia. lia. rewrite (ly_errno L LY). lia. lia. exact HWa. }
    assert (T1: forall a v, sp - 64 <= a -> a + 8 <= sp -> BGU.u64_at M1 a v -> BGU.u64_at M2 a v).
    { intros a v H1a H2a Hu. eapply (L5C.u64_at_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia. exact Hu. }
    assert (WR2 : BGU.writable M2 (sp - 64) 64).
    { change (L5.writable RSEGS M2 (sp - 64) 64). eapply (L5C.writable_agree RSEGS M1 M2). intros i Hi. apply CL. lia. lia. lia. lia.
      eapply L5.writable_grows. exact GR1. exact WR64. }
    assert (AT: at_ret1 R2 M2 o (Z.of_nat n) (Z.of_nat len) sp (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18)))).
    { unfold at_ret1.
      split. { rewrite <- L5K.rl8, (RP 8%bv ltac:(cbn; tauto)), L5K.rl8. exact R1_8. }
      split. { rewrite <- L5K.rl9, (RP 9%bv ltac:(cbn; tauto)), L5K.rl9. exact R1_9. }
      split. { rewrite <- L5K.rl18, (RP 18%bv ltac:(cbn; tauto)), L5K.rl18. exact R1_18. }
      split. { rewrite <- L5K.rl2, (RP 2%bv ltac:(cbn; tauto)), L5K.rl2. exact R1_2. }
      split. apply T1; [lia|lia|exact C8]. split. apply T1; [lia|lia|exact C16]. split. apply T1; [lia|lia|exact C24]. split. apply T1; [lia|lia|exact C32]. lia. }
    (* [comment removed for export] *)
    assert (KEEP: forall a, L5C.kept L LB sp (64 + (48 + (64 + (16 + 8224)))) [(o, 32)] a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a KA. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
      rewrite PRES. apply FR1z. lia.
      { destruct CA as [IB|[[S1 S2]|IM]]. destruct IB as (bb & Hb & Hin). pose proof (LBhi bb Hb). lia. lia. rewrite (ly_img_hi L LY) in IM. lia. }
      eapply L5C.kept_inner. exact KA. lia. lia. intros _. destruct (HW a) as [X|X]. exact X. exfalso; lia. }
    (* [comment removed for export] *)
    assert (REGS: forall (R3 : bvmap 5 word) (ks : list nat),
              (forall x, In x ks -> getr R3 (reg x) = getr R2 (reg x)) -> incl [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ks ->
              getr R3 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8))) ->
              getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9))) -> getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R (reg 18))) ->
              regs_preserved R R3).
    { intros R3 ks K3 Hincl S2 S8 S9 S18. apply L5K.regs_preserved_by_index. intros i Hi.
      cbn in Hi. destruct Hi as [<-|Hi]. { rewrite S2, <- H2, L5K.rl2. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 3%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl3, (RP 3%bv) by (cbn; tauto). rewrite L5K.rl3. apply (K1 3%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite (K3 4%nat) by (apply Hincl; cbn; tauto). rewrite <- L5K.rl4, (RP 4%bv) by (cbn; tauto). rewrite L5K.rl4. apply (K1 4%nat). apply L5K.In_of_mem; reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S8. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S9. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      destruct Hi as [<-|Hi]. { rewrite S18. symmetry. apply BGU.word_of_unsigned. reflexivity. }
      assert (G: forall j, In j [19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg j) = getr R (reg j)).
      { intros j Hj.
        assert (M2j: In j ks) by (apply Hincl; cbn in Hj |- *; tauto).
        assert (M1j: In j KS1) by (pose proof Hj as H'; L5K.inlist H').
        assert (MCj: In j L5K.CS) by (pose proof Hj as H'; L5K.inlist H').
        rewrite (K3 j M2j). rewrite (L5K.regs_preserved_index R1 R2 j RP MCj). apply (K1 j M1j). }
      apply G. L5K.inlist Hi. }
    destruct (Z_lt_le_dec (Z.of_nat len) (Z.of_nat n)) as [GROWS | KEEPS].
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (CASES:
        (exists fb2 cap2 q2, L5.big_at RSEGS M2 o (L5.BO fb2 len (L5.BDyn cap2 q2)) /\ Z.of_nat n <= cap2 /\ L5.limbs_at RSEGS M2 q2 ws /\ L5.defined M2 q2 (8 * cap2)
            /\ q2 + 8 * cap2 <= hl_ceil L /\ 4096 <= q2
            /\ ((g = Same /\ sto = L5.BDyn cap2 q2 /\ fb2 = fb /\ In (q2, 8 * cap2) LB)
                \/ (g = Grown q2 cap2 /\ fb2 = Z.lor fb 1 /\ (exists v0 v1, sto = L5.BInl v0 v1) /\ LB' = (q2, 8 * cap2) :: LB)))
        \/ (g = Same /\ (exists v0 v1, sto = L5.BInl v0 v1 /\ L5.big_at RSEGS M2 o (L5.BO fb len (L5.BInl v0 v1))) /\ (n <= 2)%nat)).
      { destruct g as [|A cap].
        - destruct POST as (HG & _ & _ & OB2 & _). destruct sto as [v0 v1|cap q].
          + right. split. reflexivity. split. exists v0, v1. split. reflexivity. exact OB2.
            destruct HG as [HG|HG]. unfold L5.bo_dyn in HG. cbn [L5.bo_fb] in HG. destruct OST as (B1 & _). rewrite B1 in HG. discriminate. lia.
          + left. exists fb, cap, q. destruct OST as (B0 & Q16 & Q24 & Hlc & Hc & Aq & Qlo & Qhi).
            specialize (BLK cap q eq_refl).
            pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ BLK) as ((QR0 & QR1 & _ & _ & QR4) & QD & _). cbn [fst snd] in QR0, QR1, QR4, QD.
            rewrite (ly_img_lo L LY), (ly_img_hi L LY) in QR1.
            assert (QK: forall a, q <= a < q + 8 * cap -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
            { intros a Ha. apply KEEP. eapply L5C.kept_block. exact BLK. lia. lia. lia. rewrite (ly_errno L LY). lia.
              apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
            split. exact OB2. split. { apply CAP. unfold L5.bo_dyn. cbn. exact B0. }
            split. { eapply (L5C.limbs_at_agree RSEGS M M2). intros i Hi. apply QK. lia. lia. lia. exact Vws. }
            split. { eapply (L5C.defined_agree M M2). intros i Hi. apply QK. lia. exact QD. }
            split. lia. split. lia. left. split. reflexivity. split. reflexivity. split. reflexivity. exact BLK.
        - destruct POST as (B0 & H3 & Hcap & HLB' & Hcr' & FB & (v0 & v1 & Hsto & FA0 & FA8) & OB2 & _).
          left. exists (Z.lor fb 1), cap, A. pose proof FB as ((BR0 & BR1 & BR2 & BR3 & BR4) & BA & DEFA).
          rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1.
          pose proof (L5ARESU.round_up_bounds (Z.of_nat n) ltac:(lia)) as [RB RM].
          split. exact OB2. split. lia.
          split. { cbn in Hsto. subst sto. rewrite Vws. destruct len as [|[|[|k]]]; cbn.
                   apply L5C.limbs_at_nil.
                   intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. replace (A + 8 * Z.of_nat 0) with A by lia. exact FA0.
                   intros i Hi. cbn in Hi. destruct i as [|[|i]]; [| |lia]; cbn. replace (A + 8 * Z.of_nat 0) with A by lia. exact FA0.
                   replace (A + 8 * Z.of_nat 1) with (A + 8) by lia. exact FA8.
                   destruct OST as (_ & _ & _ & Hl2 & _). lia. }
          split. exact DEFA. split. lia. split. lia.
          right. split. reflexivity. split. reflexivity. split. exists v0, v1. exact Hsto. exact HLB'. }
      destruct CASES as [(fb2 & cap2 & q2 & OB2 & Hn2 & LIMBS & QDEF & QHI & QLO & WHICH) | (HG & (v0 & v1 & Hsto & OB2) & Hn2)].
      * (* [comment removed for export] *)
        destruct OB2 as (Q0 & Hfb2 & Q8 & B02 & Q16 & Q24 & Hlc2 & Hc2 & Aq2 & Qlo2 & Qhi2 & HAP2). cbn [L5.bo_fb L5.bo_len] in Q0, Hfb2, Q8, B02, Hlc2.
        assert (WO8: BGU.writable M2 (o + 8) 8).
        { change (L5.writable RSEGS M2 (o + 8) 8). apply L5C.writable_of_defined; [|lia|lia]. eapply L5KU.u64_at_defined. exact Q8. unfold L5KU.IMG_HI; lia. lia. }
        destruct (p2b_run fx2 R2 M2 o (Z.of_nat n) (Z.of_nat len) sp fb2 q2 _ _ _ _ AT ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo ltac:(lia) WO8
                    Q0 Hfb2 B02 Q24 ltac:(lia) ltac:(lia))
          as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_10 & R3_11 & R3_12 & D8 & MF3 & GR3).
        assert (MF3z: forall a, 0 <= a < 2 ^ 64 -> ~ (o + 8 <= a < o + 16) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha Hna. apply MF3. rewrite BGU.unsigned_lit by lia. exact Hna. }
        destruct (memset_run fx3 R3 M3 (q2 + 8 * Z.of_nat len) (8 * (Z.of_nat n - Z.of_nat len)) r R3_10 R3_11 R3_12
                    ltac:(rewrite R3_1; f_equal; exact E1) RA ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(apply L5C.writable_of_defined; [|lia|lia]; eapply (L5C.defined_agree M2 M3); [intros i Hi; apply MF3z; lia|];
                          eapply L5.defined_sub; [exact QDEF|lia|lia]))
          as (R4 & MS4 & K4 & R4_10).
        set (M4 := wbytes M3 (Z_to_bv 64 (q2 + 8 * Z.of_nat len)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * (Z.of_nat n - Z.of_nat len))))) in MS4.
        assert (M4out: forall a k, 0 <= a < 2 ^ 64 -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= q2 + 8 * Z.of_nat len \/ q2 + 8 * Z.of_nat n <= a) ->
                       rdn RSEGS M4 (Z_to_bv 64 a) k = rdn RSEGS M3 (Z_to_bv 64 a) k).
        { intros a k Ha Hk Hap. subst M4. apply L5K.wbytes_fill_out; rewrite ?Z2Nat.id by lia; lia. }
        assert (M4b: forall a, 0 <= a < 2 ^ 64 -> ~ (q2 + 8 * Z.of_nat len <= a < q2 + 8 * Z.of_nat n) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
        { intros a Ha Hna. subst M4. apply AX2S.wbytes_out; rewrite ?BGU.unsigned_lit, ?repeat_length, ?Z2Nat.id by lia; lia. }
        assert (GR4: mem_grows M3 M4) by (subst M4; apply wbytes_grows).
        eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. { eapply msteps_trans. exact MS3. exact MS4. }
        (* [comment removed for export] *)
        assert (LIMBS4: L5.limbs_at RSEGS M4 q2 (resize_limbs ws n)).
        { rewrite resize_limbs_long by lia. apply L5C.limbs_at_app.
          - intros i Hi. unfold L5.u64_at. rewrite M4out; [|lia|lia|lia]. eapply BGU.u64_at_frame. lia. lia. intros j Hj. apply MF3z; lia. apply LIMBS. exact Hi.
          - rewrite Lws. apply L5C.limbs_at_zeros. intros i Hi. subst M4.
            replace (q2 + 8 * Z.of_nat len + 8 * Z.of_nat i) with (q2 + 8 * Z.of_nat len + 8 * Z.of_nat i) by lia.
            apply (L5K.u64_zero_of_fill RSEGS M3 (q2 + 8 * Z.of_nat len) _ (8 * Z.of_nat i)); rewrite ?Z2Nat.id by lia; lia. }
        (* [comment removed for export] *)
        assert (HDR4: L5.big_at RSEGS M4 o (L5.BO fb2 n (L5.BDyn cap2 q2))).
        { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
          split. { unfold L5.u8_at. rewrite M4out by lia. eapply BGU.u8_at_frame. apply MF3z; lia. exact Q0. }
          split. exact Hfb2. split. { unfold L5.u64_at. rewrite M4out by lia. exact D8. }
          split. exact B02.
          split. { unfold L5.u64_at. rewrite M4out by lia. eapply BGU.u64_at_frame. lia. lia. intros j Hj; apply MF3z; lia. exact Q16. }
          split. { unfold L5.u64_at. rewrite M4out by lia. eapply BGU.u64_at_frame. lia. lia. intros j Hj; apply MF3z; lia. exact Q24. }
          repeat split; try lia. exact HAP2. }
        assert (RP4: regs_preserved R R4).
        { apply (REGS R4 [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat).
          { intros x Hx. assert (HxC: In x L5K.CS) by (pose proof Hx as H'; L5K.inlist H'). assert (HxB: In x KSB) by (pose proof Hx as H'; L5K.inlist H').
            rewrite (K4 x HxC). apply K3. exact HxB. }
          intros x Hx. exact Hx.
          rewrite (K4 2%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_2.
          rewrite (K4 8%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_8.
          rewrite (K4 9%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_9.
          rewrite (K4 18%nat) by (apply L5K.In_of_mem; reflexivity). exact R3_18. }
        (* [comment removed for export] *)
        assert (KEEP4: forall a, L5C.kept L LB sp (64 + (48 + (64 + (16 + 8224)))) [(o, 32)] a -> ~ (q2 + 8 * Z.of_nat len <= a < q2 + 8 * Z.of_nat n) ->
                        M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a KA Hna. pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
          rewrite M4b by lia. rewrite MF3z by lia. apply KEEP. exact KA. }
        assert (SDEF4: L5.defined M4 (sp - (64 + (48 + (64 + (16 + 8224))))) (64 + (48 + (64 + (16 + 8224))))).
        { intros i Hi. rewrite M4b by lia. rewrite MF3z by lia.
          destruct (Z_lt_le_dec (sp - (64 + (48 + (64 + (16 + 8224)))) + i) (sp - 64)) as [Hlt|Hge].
          - replace (sp - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - 64 - (48 + (64 + (16 + 8224))) + i) by lia. apply SDEF. lia.
          - rewrite CL by lia. apply GR1. apply DEF. lia. }
        assert (HH4: forall LBx crx, hi_heap HI LBx crx M2 (m_vmmaps model2) -> In (q2, 8 * cap2) LBx -> hi_heap HI LBx crx M4 (m_vmmaps model2)).
        { intros LBx crx HHx Hin. eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HHx. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
          intros a Ha. destruct (Z_lt_le_dec a (o + 8)) as [X|X].
          { destruct (Z_lt_le_dec a (q2 + 8 * Z.of_nat len)) as [Y|Y]. left. rewrite M4b by lia. apply MF3z; lia.
            destruct (Z_lt_le_dec a (q2 + 8 * Z.of_nat n)) as [Y'|Y']. right; right. exists (q2, 8 * cap2). split. exact Hin. cbn. lia.
            left. rewrite M4b by lia. apply MF3z; lia. }
          destruct (Z_lt_le_dec a (o + 16)) as [Y|Y]. right; left. lia. left. rewrite M4b by lia. apply MF3z; lia.
          subst M4. intros x Hx. pose proof (wbytes_grows (repeat (Z_to_bv 8 0) (Z.to_nat (8 * (Z.of_nat n - Z.of_nat len)))) M3 (Z_to_bv 64 (q2 + 8 * Z.of_nat len))) as WG.
          apply WG. apply GR3. exact Hx. }
        destruct WHICH as [(-> & Hsto & -> & BLKq) | (-> & -> & (v0 & v1 & Hsto) & ->)].
        -- (* [comment removed for export] *)
           destruct POST as (HG & -> & -> & _ & _).
           apply (KONT fx3 R4 M4 model2 Same LB cr).
           ++ split. exact RP4. cbn [resize_post]. split. { left. subst sto. unfold L5.bo_dyn. cbn. exact B02. }
              split. reflexivity. split. reflexivity.
              split. { exists (L5.BDyn cap2 q2). split. exact HDR4. split.
                       split. { rewrite resize_limbs_length. reflexivity. } split. { apply resize_limbs_range. exact Rws. } cbn. exact LIMBS4.
                       subst sto. cbn. split; reflexivity. }
              split.
              ** intros a KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA.
                 pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. apply L5C.outside_cons_inv in OW2 as [NW2 _].
                 unfold L5.in_rng in NW, NW2. subst sto. cbn [fst snd L5.bo_data L5.bo_len L5.bo_st] in NW, NW2.
                 apply KEEP4. eapply L5C.kept_inner. exact KA. lia. lia. intros _. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. lia.
              ** split. { unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF4. }
                 intros a Ha CA NE DM. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR4. apply GR3. apply CD2; assumption.
           ++ exact MBV.
           ++ apply HH4. exact HH2. exact BLKq.
        -- (* [comment removed for export] *)
           destruct POST as (B0 & H3 & Hcap & HLB' & -> & FB & _ & _ & _).
           apply (KONT fx3 R4 M4 model2 (Grown q2 cap2) ((q2, 8 * cap2) :: LB) (debit L cr (8 * cap2))).
           ++ split. exact RP4. cbn [resize_post]. split. exact B0. split. lia. split. exact Hcap. split. reflexivity. split. reflexivity.
              split. { destruct FB as (FB1 & FB2 & FB3). split. exact FB1. split. exact FB2.
                       eapply L5.defined_grows. exact GR4. eapply L5.defined_grows. exact GR3. exact FB3. }
              split. exact HDR4.
              split. { split. { rewrite resize_limbs_length. reflexivity. } split. { apply resize_limbs_range. exact Rws. } cbn. exact LIMBS4. }
              split.
              ** intros a KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA.
                 pose proof (L5C.fresh_block_bounds L LB _ _ _ FB) as (FBR0 & FBR1 & FBR2 & FBR3 & FBR4).
                 pose proof (L5C.kept_not_fresh L LB sp _ [(o, 32)] a q2 (8 * cap2) KA (proj1 (proj2 FB)) FBR1 FBR4 LBhi) as NA.
                 apply KEEP4. exact KA. lia.
              ** split. { unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. exact SDEF4. }
                 intros a Ha CA NE DM. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR4. apply GR3. apply CD2; assumption.
           ++ exact MBV.
           ++ apply HH4. exact HH2. left; reflexivity.
      * (* [comment removed for export] *)
        subst g. destruct POST as (HG & -> & -> & _ & _). subst sto.
        destruct OST as (B0 & O16 & O24 & Hl2 & Rv0 & Rv1).
        destruct OB2 as (Q0 & _ & Q8 & B02 & Q16 & Q24 & _). cbn [L5.bo_fb L5.bo_len] in Q0, Q8, B02, Q16, Q24.
        assert (WO24: BGU.writable M2 (o + 8) 24).
        { change (L5.writable RSEGS M2 (o + 8) (8 + (8 + 8))). apply L5C.writable_app. lia. lia. lia. lia.
          apply L5C.writable_of_defined; [|lia|lia]. eapply L5KU.u64_at_defined. exact Q8. unfold L5KU.IMG_HI; lia. lia.
          apply L5C.writable_app. lia. lia. lia. lia.
          apply L5C.writable_of_defined; [|lia|lia]. replace (o + 8 + 8) with (o + 16) by lia. eapply L5KU.u64_at_defined. exact Q16. unfold L5KU.IMG_HI; lia. lia.
          apply L5C.writable_of_defined; [|lia|lia]. replace (o + 8 + 8 + 8) with (o + 24) by lia. eapply L5KU.u64_at_defined. exact Q24. unfold L5KU.IMG_HI; lia. lia. }
        destruct (p2c_run fx2 R2 M2 o (Z.of_nat n) (Z.of_nat len) sp fb _ _ _ _ r AT ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo ltac:(lia) WO24
                    Q0 Hfb B02 E1 RA)
          as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & D8 & D16 & D24 & MF3 & GR3).
        assert (MF3z: forall a, 0 <= a < 2 ^ 64 -> ~ (o + 8 <= a < o + 16) -> ~ (o + 16 + 8 * Z.of_nat len <= a < o + 32) -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
        { intros a Ha Hna Hnb. apply MF3; rewrite BGU.unsigned_lit by lia. exact Hna. exact Hnb. }
        eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
        apply (KONT fx3 R3 M3 model2 Same LB cr).
        -- split. { apply (REGS R3 KSC0 K3). intros x Hx. L5K.inlist Hx. exact R3_2. exact R3_8. exact R3_9. exact R3_18. }
           cbn [resize_post]. split. right. lia. split. reflexivity. split. reflexivity.
           split.
           { (* [comment removed for export] *)
             exists (L5.BInl (if Nat.eqb len 0 then 0 else v0) 0).
             assert (V0: BGU.u64_at M3 (o + 16) (if Nat.eqb len 0 then 0 else v0)).
             { destruct len as [|k]. cbn. apply D16. reflexivity. cbn [Nat.eqb].
               eapply (BGU.u64_at_frame M2 M3). lia. lia. intros j Hj. apply MF3z; lia. exact Q16. }
             split.
             - unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
               split. { eapply (BGU.u8_at_frame M2 M3). apply MF3z; lia. exact Q0. }
               split. exact Hfb. split. exact D8. split. exact B02. split. exact V0. split. exact D24.
               split. lia. split. destruct (Nat.eqb len 0); lia. lia.
             - split. 2: exact I.
               split. { rewrite resize_limbs_length. reflexivity. } split. { apply resize_limbs_range. exact Rws. }
               cbn [L5.bo_st L5.bo_len]. rewrite Vws. rewrite resize_limbs_long by (rewrite length_firstn; cbn; lia).
               rewrite length_firstn. cbn [length].
               destruct len as [|[|k]]; [| |lia]; destruct n as [|[|[|m]]]; try lia; reflexivity. }
           split.
           ++ intros a KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA.
              pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW _]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
              rewrite MF3z by lia. apply KEEP. eapply L5C.kept_inner. exact KA. lia. lia. intros _. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil.
           ++ split.
              { unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi.
                rewrite MF3z by lia.
                destruct (Z_lt_le_dec (sp - (64 + (48 + (64 + (16 + 8224)))) + i) (sp - 64)) as [Hlt|Hge].
                ** replace (sp - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - 64 - (48 + (64 + (16 + 8224))) + i) by lia. apply SDEF. lia.
                ** rewrite CL by lia. apply GR1. apply DEF. lia. }
              intros a Ha CA NE DM. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR3. apply CD2; assumption.
        -- exact MBV.
        -- eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
           intros a Ha. destruct (Z_lt_le_dec a (o + 8)) as [X|X]. left. apply MF3z; lia.
           destruct (Z_lt_le_dec a (o + 32)) as [Y|Y]. right; left. lia. left. apply MF3z; lia. exact GR3.
    + (* [comment removed for export] *)
      destruct g as [|A cap].
      2: { destruct POST as (B0 & H3 & _). exfalso. destruct sto as [v0 v1|cap' q]. destruct OST as (_ & _ & _ & Hl2 & _). lia.
           unfold L5.bo_dyn in B0. cbn [L5.bo_fb] in B0. destruct OST as (B1 & _). rewrite B1 in B0. discriminate. }
      destruct POST as (HG & -> & -> & OB2 & _).
      assert (WO8: BGU.writable M2 (o + 8) 8).
      { change (L5.writable RSEGS M2 (o + 8) 8). apply L5C.writable_of_defined; [|lia|lia]. destruct OB2 as (_ & _ & Q8 & _).
        eapply L5KU.u64_at_defined. exact Q8. unfold L5KU.IMG_HI; lia. lia. }
      destruct (p2a_run fx2 R2 M2 o (Z.of_nat n) (Z.of_nat len) sp r _ _ _ _ AT ltac:(lia) ltac:(lia) A16 ltac:(lia) ltac:(lia) WR2 Ao Olo ltac:(lia) WO8 E1 RA)
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & D8 & MF3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 Same LB cr).
      * split. { apply (REGS R3 KSA K3). intros x Hx. L5K.inlist Hx. exact R3_2. exact R3_8. exact R3_9. exact R3_18. }
        cbn [resize_post].
        split. { destruct HG as [HG|HG]. left; exact HG. right; lia. }
        split. reflexivity. split. reflexivity.
        split.
        { exists sto. split.
          - (* [comment removed for export] *)
            destruct OB2 as (Q0 & _ & Q8 & QST). unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
            split. { eapply (BGU.u8_at_frame M2 M3). apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact Q0. }
            split. exact Hfb. split. exact D8.
            destruct sto as [v0 v1|cap q].
            + destruct QST as (B0 & Q16 & Q24 & Hl2 & Rv0 & Rv1). split. exact B0.
              split. { eapply (BGU.u64_at_frame M2 M3). lia. lia. intros i Hi; apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact Q16. }
              split. { eapply (BGU.u64_at_frame M2 M3). lia. lia. intros i Hi; apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact Q24. }
              repeat split; lia.
            + destruct QST as (B0 & Q16 & Q24 & Hlc & Hc & Aq & Qlo & Qhi & HAP). split. exact B0.
              split. { eapply (BGU.u64_at_frame M2 M3). lia. lia. intros i Hi; apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact Q16. }
              split. { eapply (BGU.u64_at_frame M2 M3). lia. lia. intros i Hi; apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact Q24. }
              repeat split; try lia. exact HAP.
          - split.
            + (* [comment removed for export] *)
              rewrite resize_limbs_short by lia. split. { rewrite length_firstn. cbn [L5.bo_len]. lia. }
              split. { apply Forall_forall. intros x Hx. rewrite Forall_forall in Rws. apply Rws. exact (in_firstn x ws n Hx). }
              cbn [L5.bo_st L5.bo_len]. destruct sto as [v0 v1|cap q].
              * rewrite Vws. cbn [L5.bo_len]. apply L5C.firstn_firstn_le. lia.
              * apply L5C.limbs_at_firstn. destruct OST as (B0 & Q16 & Q24 & Hlc & Hc & Aq & Qlo & Qhi).
                specialize (BLK cap q eq_refl). pose proof (LBhi _ BLK) as QB. cbn [fst snd] in QB.
                pose proof (proj1 (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ BLK)) as (QR0 & QR & _). cbn [fst snd] in QR0, QR. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in QR.
                eapply (L5C.limbs_at_agree RSEGS M M3). 2: lia. 2: lia. 2: exact Vws.
                intros i Hi. rewrite (MF3 (Z_to_bv 64 i)) by (rewrite BGU.unsigned_lit by lia; lia).
                apply KEEP. eapply L5C.kept_block. exact BLK. lia. lia. lia. rewrite (ly_errno L LY). lia.
                apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil.
            + destruct sto; cbn; auto.
        }
        (* [comment removed for export] *)
        split.
        -- intros a KA. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in KA.
           pose proof KA as (Ha & CA & NE & OW). apply L5C.outside_cons_inv in OW as [NW OW2]. unfold L5.in_rng in NW. cbn [fst snd] in NW.
           rewrite (MF3 (Z_to_bv 64 a)) by (rewrite BGU.unsigned_lit by lia; lia).
           apply KEEP. eapply L5C.kept_inner. exact KA. lia. lia. intros _. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil.
        -- split.
           { unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi.
             rewrite (MF3 (Z_to_bv 64 _)) by (rewrite BGU.unsigned_lit by lia; lia).
             destruct (Z_lt_le_dec (sp - (64 + (48 + (64 + (16 + 8224)))) + i) (sp - 64)) as [Hlt|Hge].
             ++ replace (sp - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - 64 - (48 + (64 + (16 + 8224))) + i) by lia. apply SDEF. lia.
             ++ rewrite CL by lia. apply GR1. apply DEF. lia. }
           intros a Ha CA NE DM. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in CA. apply GR3. apply CD2; assumption.
      * exact MBV.
      * eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH2. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
        intros a Ha. destruct (Z_lt_le_dec a (o + 8)) as [X|X]. left. apply MF3; rewrite BGU.unsigned_lit by lia; lia.
        destruct (Z_lt_le_dec a (o + 16)) as [Y|Y]. right; left. lia. left. apply MF3; rewrite BGU.unsigned_lit by lia; lia. exact GR3.
Qed.

End WithHeap.
End SCFG_1.

End L5RSZU.
