(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_20088_210bc Src0_code_21134_21d54 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkReduce BigModel BigFactsDigits
     L5Defs L5Core L5CoreKit L5CoreSpecs L5KnP L5ParseArith L5ParseKit L5ParseSpecs L5TobigA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5TOB.
Import L5CS L5PS L5TB.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition RET3 : Z := 0x21b8c.  Definition AFT3 : Z := 0x21b7c.
Definition RET4 : Z := 0x20ba4.  Definition AFT4 : Z := 0x20b94.
Ltac uscr := unfold TOBIG_SCR, DETAIL_SCR, ADDD_SCR, MUL10_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.

Lemma ret3 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RET3 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RET3 W_21b8c r F_21b8c eq_refl D_21b8c H1 Hr He). Qed.
Lemma ret4 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R RET4 M) (st fx R r M).
Proof. intros H1 Hr He. apply (BRED.ret_to fx R M RET4 W_20ba4 r F_20ba4 eq_refl D_20ba4 H1 Hr He). Qed.
Lemma lit_of_word (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma wrange (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia. Qed.
Lemma ra_ok_lit z : 0 <= z < 2 ^ 47 -> z mod 2 = 0 -> L5.ra_ok z.
Proof. intros; split; assumption. Qed.
Lemma bytes_at_tail M p c t : L5.bytes_at RSEGS M p (c :: t) -> L5.bytes_at RSEGS M (p + 1) t.
Proof. intros H i Hi. replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (S i)) by lia. apply (H (S i)). cbn. lia. Qed.
Lemma obj_limbs_agree M M' b ws :
  L5C.obj_limbs RSEGS M b ws ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> L5C.agree_on M M' q (8 * Z.of_nat (length ws)) /\ 0 <= q /\ q + 8 * Z.of_nat (length ws) <= 2 ^ 64) ->
  L5C.obj_limbs RSEGS M' b ws.
Proof.
  intros (L1 & L2 & L3) HQ. split. exact L1. split. exact L2. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:EB. exact L3.
  destruct (HQ cap q eq_refl) as (AG & Q0 & Q1). eapply (L5C.limbs_at_agree RSEGS M M'). exact AG. exact Q0. exact Q1. exact L3.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis Hdet : detail_spec L HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L.

Lemma IMGLO : 0 <= hl_img_lo L <= hl_img_hi L. Proof. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma IMGHI : hl_img_hi L <= 0x7fff7f800000. Proof. rewrite (ly_img_hi L LY). lia. Qed.
Lemma ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L. Proof. rewrite (ly_errno L LY), (ly_img_lo L LY), (ly_img_hi L LY). lia. Qed.
Lemma credit_le_refl c : credit_le c c. Proof. unfold credit_le. lia. Qed.
Lemma vblk_pos m : 0 <= vblk m.
Proof. unfold vblk. destruct (m <? 39)%nat. lia. pose proof (round_up_ge_S (num_words_est m)). lia. Qed.
Lemma parse_debit_le c m : credit_le (parse_debit L c m) c.
Proof. unfold parse_debit, credit_le, debit. cbn. pose proof (vblk_pos m). lia. Qed.

(* [comment removed for export] *)
Ltac tobig_tac p0 p1m p1l p1h p2 retl KS1M :=
  intros fx R M model K LB cr p o sp r fb s HH MOK HK0 H10 H11 Ho Hlen CRED H1 RA H2 H3 H4 STK OB Hfb3 Ao Olo Ohi WO BY SR Plo Phi DAT APO KONT;
  pose proof MOK as (Mh & Ml & Mm); pose proof STK as (A16 & SLO & SHI & STOP & DEF); pose proof RA as [Hr He]; uscr;
  pose proof (L5PK.lb_wf_of_heap L HI LB cr M _ HIok HH) as LBWF;
  rewrite L5CoreKit.L5K.rl10 in H10; rewrite L5CoreKit.L5K.rl11 in H11; rewrite L5CoreKit.L5K.rl1 in H1; rewrite L5CoreKit.L5K.rl2 in H2;
  rewrite L5CoreKit.L5K.rl3 in H3; rewrite L5CoreKit.L5K.rl4 in H4.

Theorem tobig3_ok : tobig3_spec L HI.
Proof.
  unfold tobig3_spec, tobig_spec_at. tobig_tac pt0_conc pt1m_conc pt1pl_conc pt1ph_conc pt2_conc ret3 KS_P1M.
  rewrite L5CoreKit.L5K.rl12 in Ho.
  destruct s as [|c t].
  { (* [comment removed for export] *)
    cbn [length Z.of_nat] in H11.
    destruct (pt0_conc fx R M sp H2 H11 ltac:(lia) ltac:(lia) A16) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_11 & FR1 & GR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
    { eapply msteps_trans. unfold TOBIG3. exact MS1. apply ret3. rewrite R1_1. exact H1. exact Hr. exact He. }
    apply (KONT fx1 R1 M1 model LB cr).
    - unfold tobig_post. cbv zeta. split.
      { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. destruct (Nat.eq_dec i 2) as [->|NE]. rewrite R1_2, H2; reflexivity.
        apply K1. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [first [apply L5KP.In_of_existsb; reflexivity | exfalso; lia] |]). destruct Hi. }
      right. split. left. reflexivity. split. rewrite L5CoreKit.L5K.rl11. exact R1_11.
      split. reflexivity. split. { eapply (L5C.big_at_agree RSEGS M M1). intros i Hi; apply FR1. lia. lia. exact OB. }
      split. apply parse_debit_le.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [] M M M1 []). exact LBWF. uscr; lia. apply L5PK.hpres_refl. uscr. exact DEF.
      intros x Hx. apply FR1. exact GR1. constructor.
    - apply L5C.model_but_vm_refl.
    - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia. intros x Hx. apply FR1. exact GR1. constructor. }
  (* [comment removed for export] *)
  set (neg := fst (split_sign (c :: t))). set (ds := snd (split_sign (c :: t))). set (p' := if neg then p + 1 else p).
  assert (SPLIT: (c = 45 /\ neg = true /\ ds = t /\ p' = p + 1) \/ (c <> 45 /\ neg = false /\ ds = c :: t /\ p' = p)).
  { subst neg ds p'. unfold split_sign. destruct (Z.eqb_spec c 45) as [E|NE]. left. subst c. cbn. repeat split; reflexivity. right. cbn. repeat split; auto. }
  assert (WR16: L5.writable RSEGS M (sp - 16) 16).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  pose proof (BY 0%nat ltac:(cbn; lia)) as B0. cbn [nth] in B0. rewrite Z.add_0_r in B0.
  pose proof Hlen as HlenS. pose proof Phi as PhiS. cbn [length] in HlenS, PhiS.
  pose proof (proj1 (Forall_nth _ _) SR 0%nat 0 ltac:(cbn; lia)) as C0. cbn in C0.
  assert (PAPART: sp + -16 + 16 <= p + 0 \/ p + 0 + 1 <= sp + -16).
  { destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2, HAk. lia. lia. lia. }
  assert (STEP1: exists (fx1 : FPState) R1 M1,
     msteps RSEGS (st fx R TOBIG3 M) (st fx1 R1 DETAIL M1)
     /\ (forall i, In i KS_P1M -> getr R1 (reg i) = getr R (reg i))
     /\ getr R1 (reg 1) = Z_to_bv 64 AFT3 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 16)
     /\ getr R1 (reg 10) = Z_to_bv 64 p' /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (length ds)) /\ getr R1 (reg 12) = Z_to_bv 64 (if neg then 1 else 0) /\ getr R1 (reg 13) = Z_to_bv 64 o
     /\ L5.u64_at RSEGS M1 (sp - 8) r
     /\ (forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> M1 x = M x) /\ mem_grows M M1).
  { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite En, Ed, Ep.
    - subst c. destruct (pt1m_conc fx R M sp p (Z.of_nat (length (45 :: t))) o H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                           ltac:(cbn [length]; lia) ltac:(lia) B0 PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
      exists fx1, R1, M1. split. exact MS1. split. exact K1. split. exact R1_1. split. exact R1_2. split. exact R1_10.
      split. { rewrite R1_11. f_equal. cbn [length]. lia. } split. exact R1_12. split. exact R1_13.
      split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1.
    - destruct (Z_lt_le_dec c 45) as [LT|GE].
      + destruct (pt1pl_conc fx R M sp p (Z.of_nat (length (c :: t))) o c H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                             ltac:(cbn [length]; lia) ltac:(lia) B0 ltac:(lia) PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
        exists fx1, R1, M1. split. exact MS1. split. { intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [apply L5KP.In_of_existsb; reflexivity|]). destruct Hi. }
        split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split. exact R1_12. split. exact R1_13.
        split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1.
      + destruct (pt1ph_conc fx R M sp p (Z.of_nat (length (c :: t))) o c H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                             ltac:(cbn [length]; lia) ltac:(lia) B0 ltac:(lia) PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
        exists fx1, R1, M1. split. exact MS1. split. { intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [apply L5KP.In_of_existsb; reflexivity|]). destruct Hi. }
        split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split. exact R1_12. split. exact R1_13.
        split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1. }
  clear B0.
  destruct STEP1 as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold TOBIG3 in MS1. exact MS1. }
  assert (AG1: forall a k, (a + k <= sp - 16 \/ sp <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k Hak Ha Hk i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. }
  assert (LDS: (length ds <= S (length t))%nat /\ Z.of_nat (length ds) = Z.of_nat (S (length t)) - (if neg then 1 else 0) /\ p' = p + (if neg then 1 else 0)).
  { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite En, Ed, Ep; cbn [length]; repeat split; lia. }
  destruct LDS as (LDS & LDZ & PEQ). cbn [length] in Hlen, Phi, APO.
  assert (BYd: L5.bytes_at RSEGS M p' ds). { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite Ed, Ep. apply (bytes_at_tail M p c t). exact BY. exact BY. }
  assert (SRd: Forall (fun c0 => 0 <= c0 < 256) ds). { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite Ed. inversion SR; assumption. exact SR. }
  assert (HP1: L5C.hpres L LB sp TOBIG_SCR [(o, 32)] M M1).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [(o,32)] M M M1 [(sp - 16, 16)]). exact LBWF. uscr; lia. apply L5PK.hpres_refl. uscr. exact DEF.
    intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR1.
    constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
  eapply (Hdet fx1 R1 M1 model K LB cr p' o (sp - 16) AFT3 fb neg ds).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) [(sp - 16, 16)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR1.
    constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - rewrite L5CoreKit.L5K.rl12. exact R1_12.
  - rewrite L5CoreKit.L5K.rl13. exact R1_13.
  - lia.
  - exact CRED.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. unfold AFT3; lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl3, (K1 3%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H3.
  - rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. eapply L5.defined_sub. exact DEF. lia. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). apply AG1; lia. lia. lia. exact OB.
  - exact Hfb3.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR1. exact WO.
  - eapply (L5C.bytes_at_agree RSEGS M M1). 2: lia. 2: lia. 2: exact BYd.
    destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2, HAk. apply AG1; lia. apply AG1; lia. apply AG1; lia.
  - exact SRd.
  - lia.
  - lia.
  - destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    right; left. exists Ab, kb. split. exact Hin. cbn in HAk. lia. right; right; left. cbn in S2. lia. right; right; right. cbn in I2. lia.
  - lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB2 cr2 DP MBV2 HH2.
    destruct DP as (RP2 & ALT).
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (TAILc: forall W ec, (W = [(o, 32)] \/ W = []) -> L5C.hpres L LB (sp - 16) DETAIL_SCR W M1 M2 -> getr R2 (reg 11) = Z_to_bv 64 ec -> (ec = 0 \/ ec = 22) ->
              exists (fx3 : FPState) R3 M3, msteps RSEGS (st fx2 R2 AFT3 M2) (st fx3 R3 r M3) /\ regs_preserved R R3 /\ getr R3 (reg 11) = Z_to_bv 64 ec
                                    /\ (forall a k, L5C.agree_on M2 M3 a k) /\ L5C.hpres L LB sp TOBIG_SCR W M M3 /\ mem_grows M2 M3).
    { intros W ec HW HPd R2_11 ECv.
      assert (WO': forall i, i < o -> L5.outside W i). { intros i Hi. destruct HW as [-> | ->]. intros r' [<-|[]]. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
      assert (AG2: forall a k, sp - 16 <= a -> a + k <= sp -> L5C.agree_on M1 M2 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPd. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply WO'. lia. }
      assert (E8: L5.u64_at RSEGS M2 (sp - 8) r). { eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact C8. }
      pose proof (RP2 2%bv ltac:(cbn; tauto)) as P2. rewrite L5CoreKit.L5K.rl2 in P2.
      destruct (pt2_conc fx2 R2 M2 sp ec r ltac:(rewrite P2; exact R1_2) R2_11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 E8 ltac:(lia))
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_11 & FR3 & GR3).
      exists fx3, R3, M3. split. { eapply msteps_trans. unfold AFT3. exact MS3. apply ret3. exact R3_1. exact Hr. exact He. }
      split. { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. destruct (Nat.eq_dec i 2) as [->|NE]. rewrite R3_2, H2; reflexivity.
        assert (In i KS_P2 /\ In i L5CoreKit.L5K.CS /\ In i KS_P1M) as (A3 & AC & A1).
        { cbn in Hi. repeat (destruct Hi as [<-|Hi]; [first [repeat split; apply L5KP.In_of_existsb; reflexivity | exfalso; lia] |]). destruct Hi. }
        rewrite (K3 i A3), (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP2 AC). apply K1. exact A1. }
      split. exact R3_11. split. intros a k i Hi; apply FR3.
      split. 2: exact GR3.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR W M M2 M3 []). exact LBWF. uscr; lia.
      eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp TOBIG_SCR W (sp - 16) DETAIL_SCR W M M1 M2). exact LBWF. uscr; lia. lia.
      { destruct HW as [-> | ->]. exact HP1. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [] M M M1 [(sp - 16, 16)]). exact LBWF. uscr; lia.
        apply L5PK.hpres_refl. uscr. exact DEF. intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR1.
        constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
      exact HPd. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia.
      { destruct HW as [-> | ->]. constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. constructor. }
      intros x Hx. apply FR3. exact GR3. constructor. }
    destruct ALT as [(DL & DG & R11 & PP)|(ND & R11 & NPP)].
    + destruct PP as (st' & OB2 & OL2 & ST2 & CR2 & HPt). rewrite L5CoreKit.L5K.rl11 in R11.
      destruct (TAILc [(o, 32)] 0 ltac:(left; reflexivity) HPt R11 ltac:(left; reflexivity)) as (fx3 & R3 & M3 & MS3 & RP3 & R3_11 & AG3 & HP3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 LB2 cr2).
      * unfold tobig_post. cbv zeta. change (snd (split_sign (c :: t))) with ds. change (fst (split_sign (c :: t))) with neg.
        split. exact RP3. left. split. { split. exact DL. exact DG. } split. { rewrite L5CoreKit.L5K.rl11. exact R3_11. }
        unfold parse_post. cbv zeta. exists st'. split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. }
        split. { eapply (obj_limbs_agree M2 M3). exact OL2. cbn [L5.bo_st]. intros cap q E. subst st'.
                 destruct OB2 as (_ & _ & _ & (_ & _ & _ & X4 & X5 & X6 & X7 & X8)). cbn [L5.bo_len] in X4. rewrite wlist_length. split. apply AG3. lia. }
        split. { destruct st' as [v0 v1|cap q]. exact ST2. destruct ST2 as (S1' & S2' & S3' & (S4' & S5' & S6')). split. exact S1'. split. exact S2'. split. exact S3'.
                 split. exact S4'. split. exact S5'. eapply (L5C.defined_agree M2 M3). apply AG3. exact S6'. }
        split. exact CR2. exact HP3.
      * exact MBV2.
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. 2: exact GR3. 2: constructor.
        intros x _. rewrite <- (lit_of_word x). apply (AG3 (bv_unsigned x) 1). pose proof (wrange x). lia.
    + destruct NPP as (ELB & OB2 & CR2 & HPt). rewrite L5CoreKit.L5K.rl11 in R11.
      destruct (TAILc [] 22 ltac:(right; reflexivity) HPt R11 ltac:(right; reflexivity)) as (fx3 & R3 & M3 & MS3 & RP3 & R3_11 & AG3 & HP3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 LB2 cr2).
      * unfold tobig_post. cbv zeta. change (snd (split_sign (c :: t))) with ds. change (fst (split_sign (c :: t))) with neg.
        split. exact RP3. right. split. exact ND. split. { rewrite L5CoreKit.L5K.rl11. exact R3_11. }
        split. exact ELB. split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. } split. exact CR2. exact HP3.
      * exact MBV2.
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. 2: exact GR3. 2: constructor.
        intros x _. rewrite <- (lit_of_word x). apply (AG3 (bv_unsigned x) 1). pose proof (wrange x). lia.
Qed.

Theorem tobig4_ok : tobig4_spec L HI.
Proof.
  unfold tobig4_spec, tobig_spec_at. tobig_tac qt0_conc qt1m_conc qt1pl_conc qt1ph_conc qt2_conc ret4 KS_Q1M.
  rewrite L5CoreKit.L5K.rl12 in Ho.
  destruct s as [|c t].
  { (* [comment removed for export] *)
    cbn [length Z.of_nat] in H11.
    destruct (qt0_conc fx R M sp H2 H11 ltac:(lia) ltac:(lia) A16) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_11 & FR1 & GR1).
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
    { eapply msteps_trans. unfold TOBIG4. exact MS1. apply ret4. rewrite R1_1. exact H1. exact Hr. exact He. }
    apply (KONT fx1 R1 M1 model LB cr).
    - unfold tobig_post. cbv zeta. split.
      { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. destruct (Nat.eq_dec i 2) as [->|NE]. rewrite R1_2, H2; reflexivity.
        apply K1. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [first [apply L5KP.In_of_existsb; reflexivity | exfalso; lia] |]). destruct Hi. }
      right. split. left. reflexivity. split. rewrite L5CoreKit.L5K.rl11. exact R1_11.
      split. reflexivity. split. { eapply (L5C.big_at_agree RSEGS M M1). intros i Hi; apply FR1. lia. lia. exact OB. }
      split. apply parse_debit_le.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [] M M M1 []). exact LBWF. uscr; lia. apply L5PK.hpres_refl. uscr. exact DEF.
      intros x Hx. apply FR1. exact GR1. constructor.
    - apply L5C.model_but_vm_refl.
    - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) []). exact HIok. exact HH. exact (ly_ro L LY). lia. intros x Hx. apply FR1. exact GR1. constructor. }
  (* [comment removed for export] *)
  set (neg := fst (split_sign (c :: t))). set (ds := snd (split_sign (c :: t))). set (p' := if neg then p + 1 else p).
  assert (SPLIT: (c = 45 /\ neg = true /\ ds = t /\ p' = p + 1) \/ (c <> 45 /\ neg = false /\ ds = c :: t /\ p' = p)).
  { subst neg ds p'. unfold split_sign. destruct (Z.eqb_spec c 45) as [E|NE]. left. subst c. cbn. repeat split; reflexivity. right. cbn. repeat split; auto. }
  assert (WR16: L5.writable RSEGS M (sp - 16) 16).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  pose proof (BY 0%nat ltac:(cbn; lia)) as B0. cbn [nth] in B0. rewrite Z.add_0_r in B0.
  pose proof Hlen as HlenS. pose proof Phi as PhiS. cbn [length] in HlenS, PhiS.
  pose proof (proj1 (Forall_nth _ _) SR 0%nat 0 ltac:(cbn; lia)) as C0. cbn in C0.
  assert (PAPART: sp + -16 + 16 <= p + 0 \/ p + 0 + 1 <= sp + -16).
  { destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2, HAk. lia. lia. lia. }
  assert (STEP1: exists (fx1 : FPState) R1 M1,
     msteps RSEGS (st fx R TOBIG4 M) (st fx1 R1 DETAIL M1)
     /\ (forall i, In i KS_Q1M -> getr R1 (reg i) = getr R (reg i))
     /\ getr R1 (reg 1) = Z_to_bv 64 AFT4 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 16)
     /\ getr R1 (reg 10) = Z_to_bv 64 p' /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (length ds)) /\ getr R1 (reg 12) = Z_to_bv 64 (if neg then 1 else 0) /\ getr R1 (reg 13) = Z_to_bv 64 o
     /\ L5.u64_at RSEGS M1 (sp - 8) r
     /\ (forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> M1 x = M x) /\ mem_grows M M1).
  { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite En, Ed, Ep.
    - subst c. destruct (qt1m_conc fx R M sp p (Z.of_nat (length (45 :: t))) o H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                           ltac:(cbn [length]; lia) ltac:(lia) B0 PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
      exists fx1, R1, M1. split. exact MS1. split. exact K1. split. exact R1_1. split. exact R1_2. split. exact R1_10.
      split. { rewrite R1_11. f_equal. cbn [length]. lia. } split. exact R1_12. split. exact R1_13.
      split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1.
    - destruct (Z_lt_le_dec c 45) as [LT|GE].
      + destruct (qt1pl_conc fx R M sp p (Z.of_nat (length (c :: t))) o c H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                             ltac:(cbn [length]; lia) ltac:(lia) B0 ltac:(lia) PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
        exists fx1, R1, M1. split. exact MS1. split. { intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [apply L5KP.In_of_existsb; reflexivity|]). destruct Hi. }
        split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split. exact R1_12. split. exact R1_13.
        split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1.
      + destruct (qt1ph_conc fx R M sp p (Z.of_nat (length (c :: t))) o c H2 H10 H11 Ho ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 WR16
                             ltac:(cbn [length]; lia) ltac:(lia) B0 ltac:(lia) PAPART) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
        exists fx1, R1, M1. split. exact MS1. split. { intros i Hi. apply K1. revert Hi. clear. intros Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [apply L5KP.In_of_existsb; reflexivity|]). destruct Hi. }
        split. exact R1_1. split. exact R1_2. split. exact R1_10. split. exact R1_11. split. exact R1_12. split. exact R1_13.
        split. { rewrite H1, BG.unsigned_lit in C8 by lia. exact C8. } split. intros x Hx. apply FR1. lia. exact GR1. }
  clear B0.
  destruct STEP1 as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & C8 & FR1 & GR1).
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. { unfold TOBIG4 in MS1. exact MS1. }
  assert (AG1: forall a k, (a + k <= sp - 16 \/ sp <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k Hak Ha Hk i Hi. apply FR1. rewrite BG.unsigned_lit by lia. lia. }
  assert (LDS: (length ds <= S (length t))%nat /\ Z.of_nat (length ds) = Z.of_nat (S (length t)) - (if neg then 1 else 0) /\ p' = p + (if neg then 1 else 0)).
  { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite En, Ed, Ep; cbn [length]; repeat split; lia. }
  destruct LDS as (LDS & LDZ & PEQ). cbn [length] in Hlen, Phi, APO.
  assert (BYd: L5.bytes_at RSEGS M p' ds). { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite Ed, Ep. apply (bytes_at_tail M p c t). exact BY. exact BY. }
  assert (SRd: Forall (fun c0 => 0 <= c0 < 256) ds). { destruct SPLIT as [(Ec & En & Ed & Ep)|(Nc & En & Ed & Ep)]; rewrite Ed. inversion SR; assumption. exact SR. }
  assert (HP1: L5C.hpres L LB sp TOBIG_SCR [(o, 32)] M M1).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [(o,32)] M M M1 [(sp - 16, 16)]). exact LBWF. uscr; lia. apply L5PK.hpres_refl. uscr. exact DEF.
    intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR1.
    constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
  eapply (Hdet fx1 R1 M1 model K LB cr p' o (sp - 16) AFT4 fb neg ds).
  - eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB cr M M1 (m_vmmaps model) [(sp - 16, 16)]). exact HIok. exact HH. exact (ly_ro L LY). lia.
    { intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. } exact GR1.
    constructor. left. cbn. lia. constructor.
  - exact MOK.
  - exact HK0.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - rewrite L5CoreKit.L5K.rl12. exact R1_12.
  - rewrite L5CoreKit.L5K.rl13. exact R1_13.
  - lia.
  - exact CRED.
  - rewrite L5CoreKit.L5K.rl1. exact R1_1.
  - apply ra_ok_lit. unfold AFT4; lia. reflexivity.
  - rewrite L5CoreKit.L5K.rl2. exact R1_2.
  - rewrite L5CoreKit.L5K.rl3, (K1 3%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H3.
  - rewrite L5CoreKit.L5K.rl4, (K1 4%nat) by (apply L5KP.In_of_existsb; reflexivity). exact H4.
  - split. { replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    uscr. split. lia. split. lia. split. lia. eapply L5.defined_grows. exact GR1. eapply L5.defined_sub. exact DEF. lia. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). apply AG1; lia. lia. lia. exact OB.
  - exact Hfb3.
  - exact Ao.
  - lia.
  - exact Ohi.
  - eapply L5.writable_grows. exact GR1. exact WO.
  - eapply (L5C.bytes_at_agree RSEGS M M1). 2: lia. 2: lia. 2: exact BYd.
    destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    pose proof (LBWF (Ab, kb) Hin) as (W0 & W1 & W2). cbn in W0, W1, W2, HAk. apply AG1; lia. apply AG1; lia. apply AG1; lia.
  - exact SRd.
  - lia.
  - lia.
  - destruct DAT as [Z0|[(Ab & kb & Hin & HA & HAk)|[[S1 S2]|[I1 I2]]]]. cbn in Z0; lia.
    right; left. exists Ab, kb. split. exact Hin. cbn in HAk. lia. right; right; left. cbn in S2. lia. right; right; right. cbn in I2. lia.
  - lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 LB2 cr2 DP MBV2 HH2.
    destruct DP as (RP2 & ALT).
    assert (MOK2: model_ok model2).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV2); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV2); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV2); exact Y3]]. }
    pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (TAILc: forall W ec, (W = [(o, 32)] \/ W = []) -> L5C.hpres L LB (sp - 16) DETAIL_SCR W M1 M2 -> getr R2 (reg 11) = Z_to_bv 64 ec -> (ec = 0 \/ ec = 22) ->
              exists (fx3 : FPState) R3 M3, msteps RSEGS (st fx2 R2 AFT4 M2) (st fx3 R3 r M3) /\ regs_preserved R R3 /\ getr R3 (reg 11) = Z_to_bv 64 ec
                                    /\ (forall a k, L5C.agree_on M2 M3 a k) /\ L5C.hpres L LB sp TOBIG_SCR W M M3 /\ mem_grows M2 M3).
    { intros W ec HW HPd R2_11 ECv.
      assert (WO': forall i, i < o -> L5.outside W i). { intros i Hi. destruct HW as [-> | ->]. intros r' [<-|[]]. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
      assert (AG2: forall a k, sp - 16 <= a -> a + k <= sp -> L5C.agree_on M1 M2 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HPd. uscr; lia. uscr; lia. lia. lia. intros i Hi. apply WO'. lia. }
      assert (E8: L5.u64_at RSEGS M2 (sp - 8) r). { eapply (L5C.u64_at_agree RSEGS M1 M2). apply AG2; lia. lia. lia. exact C8. }
      pose proof (RP2 2%bv ltac:(cbn; tauto)) as P2. rewrite L5CoreKit.L5K.rl2 in P2.
      destruct (qt2_conc fx2 R2 M2 sp ec r ltac:(rewrite P2; exact R1_2) R2_11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) A16 E8 ltac:(lia))
        as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_11 & FR3 & GR3).
      exists fx3, R3, M3. split. { eapply msteps_trans. unfold AFT4. exact MS3. apply ret4. exact R3_1. exact Hr. exact He. }
      split. { apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. destruct (Nat.eq_dec i 2) as [->|NE]. rewrite R3_2, H2; reflexivity.
        assert (In i KS_Q2 /\ In i L5CoreKit.L5K.CS /\ In i KS_Q1M) as (A3 & AC & A1).
        { cbn in Hi. repeat (destruct Hi as [<-|Hi]; [first [repeat split; apply L5KP.In_of_existsb; reflexivity | exfalso; lia] |]). destruct Hi. }
        rewrite (K3 i A3), (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP2 AC). apply K1. exact A1. }
      split. exact R3_11. split. intros a k i Hi; apply FR3.
      split. 2: exact GR3.
      eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR W M M2 M3 []). exact LBWF. uscr; lia.
      eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB sp TOBIG_SCR W (sp - 16) DETAIL_SCR W M M1 M2). exact LBWF. uscr; lia. lia.
      { destruct HW as [-> | ->]. exact HP1. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB sp TOBIG_SCR [] M M M1 [(sp - 16, 16)]). exact LBWF. uscr; lia.
        apply L5PK.hpres_refl. uscr. exact DEF. intros x Hx. apply FR1. intros Hin. apply (Hx (sp - 16, 16)). left; reflexivity. unfold L5.in_rng; cbn. lia. exact GR1.
        constructor. apply L5PK.wr_scratch; uscr; lia. constructor. }
      exact HPd. apply L5PK.lb_sub_refl. uscr; lia. lia. uscr; lia.
      { destruct HW as [-> | ->]. constructor. eapply L5PK.wr_declared. left; reflexivity. lia. lia. constructor. constructor. }
      intros x Hx. apply FR3. exact GR3. constructor. }
    destruct ALT as [(DL & DG & R11 & PP)|(ND & R11 & NPP)].
    + destruct PP as (st' & OB2 & OL2 & ST2 & CR2 & HPt). rewrite L5CoreKit.L5K.rl11 in R11.
      destruct (TAILc [(o, 32)] 0 ltac:(left; reflexivity) HPt R11 ltac:(left; reflexivity)) as (fx3 & R3 & M3 & MS3 & RP3 & R3_11 & AG3 & HP3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 LB2 cr2).
      * unfold tobig_post. cbv zeta. change (snd (split_sign (c :: t))) with ds. change (fst (split_sign (c :: t))) with neg.
        split. exact RP3. left. split. { split. exact DL. exact DG. } split. { rewrite L5CoreKit.L5K.rl11. exact R3_11. }
        unfold parse_post. cbv zeta. exists st'. split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. }
        split. { eapply (obj_limbs_agree M2 M3). exact OL2. cbn [L5.bo_st]. intros cap q E. subst st'.
                 destruct OB2 as (_ & _ & _ & (_ & _ & _ & X4 & X5 & X6 & X7 & X8)). cbn [L5.bo_len] in X4. rewrite wlist_length. split. apply AG3. lia. }
        split. { destruct st' as [v0 v1|cap q]. exact ST2. destruct ST2 as (S1' & S2' & S3' & (S4' & S5' & S6')). split. exact S1'. split. exact S2'. split. exact S3'.
                 split. exact S4'. split. exact S5'. eapply (L5C.defined_agree M2 M3). apply AG3. exact S6'. }
        split. exact CR2. exact HP3.
      * exact MBV2.
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. 2: exact GR3. 2: constructor.
        intros x _. rewrite <- (lit_of_word x). apply (AG3 (bv_unsigned x) 1). pose proof (wrange x). lia.
    + destruct NPP as (ELB & OB2 & CR2 & HPt). rewrite L5CoreKit.L5K.rl11 in R11.
      destruct (TAILc [] 22 ltac:(right; reflexivity) HPt R11 ltac:(right; reflexivity)) as (fx3 & R3 & M3 & MS3 & RP3 & R3_11 & AG3 & HP3 & GR3).
      eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
      apply (KONT fx3 R3 M3 model2 LB2 cr2).
      * unfold tobig_post. cbv zeta. change (snd (split_sign (c :: t))) with ds. change (fst (split_sign (c :: t))) with neg.
        split. exact RP3. right. split. exact ND. split. { rewrite L5CoreKit.L5K.rl11. exact R3_11. }
        split. exact ELB. split. { eapply (L5C.big_at_agree RSEGS M2 M3). apply AG3. lia. lia. exact OB2. } split. exact CR2. exact HP3.
      * exact MBV2.
      * eapply (L5PK.hi_heap_pure L IMGHI STOP ERR HI LB2 cr2 M2 M3 (m_vmmaps model2) []). exact HIok. exact HH2. exact (ly_ro L LY). lia. 2: exact GR3. 2: constructor.
        intros x _. rewrite <- (lit_of_word x). apply (AG3 (bv_unsigned x) 1). pose proof (wrange x). lia.
Qed.
End WithHeap.
End SCFG_1.

End L5TOB.
