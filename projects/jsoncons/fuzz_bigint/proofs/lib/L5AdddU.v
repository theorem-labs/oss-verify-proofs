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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore AsanPlan AsanPlanSound Ub0PlanKit AsanPlanSoundSums Ub0Sums
     BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkDivBaseU BigLinkMulAlg BigLinkMul BigLinkMulU L5Defs L5Words L5ReduceU L5ReduceGU
     L5Core L5CoreKit L5CoreKitU L5CoreSpecsU L5AReserveU L5ReserveU L5ResizePU L5ResizeU L5Mul10W L5AdddPU L5AdddTU L5AdddKU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADDU.
Import L5CSU.
Import L5ADDPU.
Import L5MULW.
Import L5ADDKU.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem addd_ok : addd_spec L HI.
Proof.
  unfold addd_spec. intros fx R M model K LB cr o d sp r b ws HH MOK HK0 H10 H11 Hd Hlen CAP CR H1 RA H2 H4 STK OB OL NEG Ao Olo Ohi WO BLK KONT.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in SLO, DEF.
  pose proof RA as [Hr He].
  assert (LBhi: forall bb, In bb LB -> fst bb + snd bb <= hl_ceil L).
  { intros bb Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) bb Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. }
  assert (LBwf: forall q c, In (q, 8 * c) LB -> (4096 <= q /\ (q + 8 * c <= 0x10000 \/ 0x92000 <= q)) /\ q + 8 * c <= hl_ceil L /\ L5.defined M q (8 * c)).
  { intros q c Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) _ Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4) & QD & _). cbn [fst snd] in Q0, Q1, Q4, QD.
    rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. split. split. exact Q0. exact Q1. split. exact Q4. exact QD. }
  assert (WR112: BGU.writable M (sp - 112) 112).
  { change (L5.writable RSEGS M (sp - 112) 112). eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. lia. lia. lia. lia. }
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). destruct OL as (Lws & Rws & Vws).
  cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data L5.bo_neg] in *.
  pose proof (words_ok_of_Forall ws Rws) as WOK. pose proof (val_bound ws WOK) as VB. rewrite Lws in VB.
  set (V := val ws) in *.
  assert (Hlen27: Z.of_nat len <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. destruct OST as (_ & _ & _ & Hl2 & _). lia. destruct OST as (_ & _ & _ & Hlc & Hc & _). lia. }
  pose proof (bv_unsigned_in_range _ (getr R (reg 1))) as RG1. pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as RG8.
  pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as RG9. pose proof (bv_unsigned_in_range _ (getr R (reg 18))) as RG18.
  pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as RG19. pose proof (bv_unsigned_in_range _ (getr R (reg 20))) as RG20.
  change (bv_modulus 64) with (2 ^ 64) in RG1, RG8, RG9, RG18, RG19, RG20.
  assert (E1 : bv_unsigned (getr R (reg 1)) = r). { rewrite <- L5K.rl1, H1. apply BGU.unsigned_lit. lia. }
  destruct (p1_run fx R M o sp fb (Z.of_nat len) H10 ltac:(lia) Ao H2 A16 ltac:(lia) ltac:(lia) WR112 Olo ltac:(lia) O0 Hfb NEG O8 ltac:(lia))
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_11 & C8 & C16 & C24 & C32 & C40 & C48 & FR1 & GR1).
  rewrite <- L5K.rl11, H11 in R1_9.
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 112 <= a < sp) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BGU.unsigned_lit by lia. exact Hna. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (L5RSZU.resize_ok L HI LY HIok fx1 R1 M1 model K LB cr o (sp - 112) RET1 (S len) (L5.BO fb len sto) ws).
  - eapply (L5C.hi_heap_client L SCFG HI LB cr M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite (ly_img_hi L LY); lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 112)) as [Hlt|Hge]. left. apply FR1z; lia.
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']. right; left. lia. left. apply FR1z; lia. exact GR1.
  - exact MOK.
  - exact HK0.
  - exact R1_10.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r. exact R1_11.
  - lia.
  - cbn [L5.bo_dyn L5.bo_cap L5.bo_fb L5.bo_st]. intros Hdy. specialize (CAP Hdy). lia.
  - intros H3 Hdy. unfold L5.bo_dyn in Hdy. cbn [L5.bo_fb] in Hdy. destruct sto as [v0 v1|cap q]. 2:{ exfalso. destruct OST as (B0 & _). rewrite B0 in Hdy. discriminate. }
    destruct OST as (_ & _ & _ & Hl2 & _). assert (L2: len = 2%nat) by lia. rewrite L2. change (8 * round_up (Z.of_nat 3)) with 64. apply CR. exact Hdy. exact L2.
  - exact R1_1.
  - split. unfold RET1. lia. reflexivity.
  - exact R1_2.
  - rewrite <- H4. apply (K1 4%nat). apply L5K.In_of_mem. reflexivity.
  - split. { replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK. split. lia. split. lia. split. lia.
    intros i Hi. apply GR1. replace (sp - 112 - (64 + (48 + (64 + (16 + 8224)))) + i) with (sp - (112 + (64 + (48 + (64 + (16 + 8224))))) + i) by lia. apply DEF. lia.
  - eapply (L5C.big_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact OB.
  - split. exact Lws. split. exact Rws. cbn [L5.bo_st L5.bo_len]. destruct sto as [v0 v1|cap q]. exact Vws.
    destruct (LBwf q cap (BLK cap q eq_refl)) as (QR & QB & QD).
    eapply (L5C.limbs_at_agree RSEGS M M1). intros i Hi. apply FR1z; lia. lia. lia. exact Vws.
  - exact Ao.
  - lia.
  - exact Ohi.
  - change (L5.writable RSEGS M1 o 32). eapply L5.writable_grows. exact GR1. exact WO.
  - exact BLK.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB' cr' POST MBV HH2.
    apply (L5ADDKU.addd_after_resize L HI LY HIok fx R M model K LB cr o d sp r fb len sto ws Hd Hlen RA H2 Lws Rws NEG Ao Olo Ohi WO BLK KONT Mh Ml A16 SLO SHI STOP DEF Hr He LBhi LBwf WR112 Hfb OST WOK VB Hlen27 RG1 RG8 RG9 RG18 RG19 RG20 E1 R1 M1 K1 R1_2 R1_8 R1_9 C8 C16 C24 C32 C40 C48 GR1 FR1z fx2 R2 M2 model2 g LB' cr' POST MBV HH2).
Qed.


End WithHeap.
End SCFG_1.

End L5ADDU.
