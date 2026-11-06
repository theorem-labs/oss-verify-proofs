(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan AsanPlanCore BigLinkBase BigModel
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5CatchP3U.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5CA3U.
Import L5CSU L5PSU L5STRKU L5E2KU L5CP3U.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).

Ltac kin K i := rewrite (K i) by (apply L5KP.In_of_existsb; reflexivity).
Ltac pr :=
  lazymatch goal with
  | |- getr _ _ = _ => first [ eassumption | etransitivity; [eassumption|]; f_equal; ring ]
  | |- L5.u64_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u64_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5.u8_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u8_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5.u32_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u32_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5.defined ?M ?a ?n => first [ eassumption
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.defined_sub M a' n' a n H); alia0 end   (* [comment removed for export] *)
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.defined_sub M a' n' a n H); alia end ]
  | |- L5.writable _ ?M ?a ?n => first [ eassumption | rewrite ?Z.add_0_l; eassumption
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.writable_sub _ M a' n' a n); [apply (L5C.writable_of_defined _ M a' n' H); alia0 | alia0 | alia0] end
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.writable_sub _ M a' n' a n); [apply (L5C.writable_of_defined _ M a' n' H); alia | alia | alia] end ]
  | |- ?a mod ?m = 0 => first [ eassumption | match goal with H : ?b mod m = 0 |- _ => replace a with b by ring; exact H end ]
  | |- L5.img_clear _ _ _ => eassumption
  | |- 0 <= U _ _ < _ => unfold U; apply wrange
  | |- 0 <= bv_unsigned _ < _ => apply wrange
  | |- _ => first [ eassumption | alia ]
  end.

Section SCFG_2.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let IMGLO := IMGLO L LY. Let IMGHI := IMGHI L LY. Let ERR := ERR L LY.
Let hi_heap_clientx := hi_heap_clientx L HI LY LYX HIok.
Let stat_keep_hpres := stat_keep_hpres L LY. Let defined_across := defined_across L LY.

Theorem catch3_ok : L5USU.catch3_spec L HI.
Proof.
  unfold L5USU.catch3_spec, L5USU.catch_spec.
  intros fx R M model K LB LBX cr obj S HH MOK HK0 H10 H2 H3 H4 STK EXC C0 U1 IC1 IC2 IC3 KE.
  pose proof MOK as (Mh & Ml & Mm).
  rewrite L5CoreKit.L5K.rl10 in H10. rewrite L5CoreKit.L5K.rl2 in H2. rewrite L5CoreKit.L5K.rl3 in H3. rewrite L5CoreKit.L5K.rl4 in H4.
  unfold L5USU.GP in H3. unfold TP in H4.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold L5USU.CATCH_SCR, HEAP_STACK in SLO, DEF.
  unfold EH_CAUGHT in C0. unfold EH_UNCAUGHT in U1.
  destruct EXC as (ref & cfa & ELBX & BOK & (HDR & VT & IMP & RS)). subst LBX.
  pose proof HDR as (Z8 & RC & TI & DT & UH & TH & Z12 & HS & AR & LS & CT & AP & EC & CL & P1 & P2).
  pose proof RS as (RL0 & RL8 & RCNT & RBY).
  unfold L5USU.TI_RUNTIME_ERROR, L5USU.TI_ASSERTION_ERROR, L5USU.DTOR_RUNTIME_ERROR, L5USU.EXC_CLASS in TI, DT, EC.
  unfold L5USU.REF1_SZ, L5USU.REF2_SZ, L5USU.REF3_SZ, L5USU.EXC1_SZ, L5USU.EXC23_SZ in *.
  destruct BOK as (O16 & OLO & OHI & OHA & R16 & RLO & RHI & RHA & APART).
  (* [comment removed for export] *)
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as [WFB [ND _]].
  destruct (WFB (ref, 66) ltac:(left; reflexivity)) as (RR & DEFr & BAr'). cbn [fst snd] in RR, DEFr, BAr'.
  destruct (WFB (obj - 128, 144) ltac:(right; left; reflexivity)) as (BR & DEFo & BAo'). cbn [fst snd] in BR, DEFo, BAo'.
  assert (DEFr': L5.defined M ref 66) by exact DEFr. assert (DEFo': L5.defined M (obj - 128) 144) by exact DEFo. clear DEFr DEFo.
  cbn [map fst app] in ND. apply stdpp.list_relations.list.NoDup_cons in ND. destruct ND as [NI ND].
  assert (NE: ref <> obj - 128). { intros E. apply NI. rewrite E. left. }
  assert (BAr: blocks_apart ref 66 LB). { intros b Hb. apply BAr'. cbn [lb_remove fst app]. rewrite Z.eqb_refl. right. exact Hb. }
  assert (BAo: blocks_apart (obj - 128) 144 LB).
  { intros b Hb. apply BAo'. cbn [lb_remove fst app]. rewrite (proj2 (Z.eqb_neq ref (obj - 128)) NE). rewrite Z.eqb_refl. right. exact Hb. }
  clear BAr' BAo'.
  pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). pose proof RR as (RR0 & RR1 & RR2 & RR3 & RR4).
  rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1, RR1. unfold hl_ceil in BR4, RR4.
  assert (LBWF: L5PK.lb_wf L LB). { intros b Hb. apply (L5PK.lb_wf_of_heap L HI _ cr M (m_vmmaps model) HIok HH). right; right. exact Hb. }
  assert (CSP16: (S - 1008) mod 16 = 0). { replace (S - 1008) with (S + (-63) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: obj mod 16 = 0). { replace obj with (obj - 128 + 8 * 16) by lia. rewrite Z_mod_plus_full. exact O16. }
  assert (Z72: L5.u32_at RSEGS M (obj - 72) 0).
  { apply u32_zero_of_bytes. intros i Hi. replace (obj - 72 + i) with (obj - 80 + (8 + i)) by lia. apply Z12. lia. lia. lia. }
  assert (WUC: L5.writable RSEGS M 459776 4). { apply (writable_img M EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; lia. }
  assert (WCA: L5.writable RSEGS M 459768 8). { apply (writable_img M EH_CAUGHT 8 wseg_caught); unfold EH_CAUGHT; lia. }
  assert (HQ: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M). { apply L5PK.hpres_refl. exact DEF. }
  assert (FRA: L5PK.fresh_rng L LB (obj - 128) 144). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. alia. exact BAo. }
  assert (FRR: L5PK.fresh_rng L LB ref 66). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact RR1. split. alia. exact BAr. }
  unfold cfg, L5USU.CATCH.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unshelve epose proof (e3b1u_conc fx R M (S - 1008) obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_10 & R1_11 & R1_12 & R1_13 & R1_14 & B584 & B576 & B80 & B72 & FR1 & GR1).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }

  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  assert (AG1: forall a k, (a + k <= (S - 96) \/ S <= a) -> (a + k <= obj - 80 \/ obj - 68 <= a) -> (a + k <= 459768 \/ 459780 <= a) ->
                0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M1 a k).
  { intros a k E1 E2 E3 Ha Hk i Hi. apply FR1; rewrite L5.unsigned_lit by alia; alia. }
  assert (DEF1: L5.defined M1 (S - 8336) 8336) by (eapply L5.defined_grows; [exact GR1 | exact DEF]).
  assert (DEFo1: L5.defined M1 (obj - 128) 144) by (eapply L5.defined_grows; [exact GR1 | exact DEFo']).
  assert (DEFr1: L5.defined M1 ref 66) by (eapply L5.defined_grows; [exact GR1 | exact DEFr']).
  assert (HH1: hi_heap HI ((ref, 66) :: (obj - 128, 144) :: LB) cr M1 (m_vmmaps model)).
  { eapply hi_heap_clientx. exact HH. alia. 2: exact GR1. intros a Ha.
    destruct (Z_lt_le_dec a 459768) as [L0|G0]. 2: destruct (Z_lt_le_dec a 459780) as [L0'|G0']. 2: { right; right; right. unfold statx, EH_CAUGHT. alia. }
    all: destruct (Z_lt_le_dec a (obj - 80)) as [L2|G2]; [| destruct (Z_lt_le_dec a (obj - 68)) as [L2'|G2']; [right; right; left; exists (obj - 128, 144); split; [right; left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a ((S - 96))) as [L3|G3]; [left; apply FR1; rewrite L5.unsigned_lit by alia; alia|].
    all: destruct (Z_lt_le_dec a (S)) as [L4|G4]; [right; left; alia| left; apply FR1; rewrite L5.unsigned_lit by alia; alia]. }
  assert (HQ1: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M1).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S 8336 _ M M M1 [((S - 96), 96); (obj + -80, 12); (0 + 459768, 8); (0 + 459776, 4)]). exact LBWF. alia. exact HQ.
    { intros x Hx. apply FR1; intros Hin.
      - apply (Hx ((S - 96), 96)). left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (obj + -80, 12)). right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (0 + 459768, 8)). right; right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (0 + 459776, 4)). right; right; right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
    exact GR1.
    constructor. apply L5PK.wr_scratch; alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. eapply L5PK.wr_declared. left; reflexivity. alia. alia.
    constructor. eapply L5PK.wr_declared. right; left; reflexivity. alia. alia.
    constructor. }
  assert (R1_3: getr R1 (reg 3) = Z_to_bv 64 67584) by (kin K1 3%nat; exact H3).
  assert (R1_4: getr R1 (reg 4) = Z_to_bv 64 462648) by (kin K1 4%nat; exact H4).
  assert (R1_8: getr R1 (reg 8) = getr R (reg 8)) by (kin K1 8%nat; reflexivity).
  assert (R1_9: getr R1 (reg 9) = getr R (reg 9)) by (kin K1 9%nat; reflexivity).
  Ltac t64 AG H := eapply (L5C.u64_at_agree RSEGS); [apply AG; alia | alia | alia | exact H].
  Ltac t32 AG H := eapply L5USU.u32_at_agree; [apply AG; alia | alia | alia | exact H].
  assert (D32: L5.u64_at RSEGS M1 (obj - 32) 4849336966747728640) by (t64 AG1 EC).
  assert (D120: L5.u64_at RSEGS M1 (obj - 120) 1) by (t64 AG1 RC).
  assert (D104: L5.u64_at RSEGS M1 (obj - 104) 256628) by (t64 AG1 DT).
  assert (D8: L5.u64_at RSEGS M1 (obj + 8) (ref + 24)) by (t64 AG1 IMP).
  assert (Dr16: L5.u32_at RSEGS M1 (ref + 16) 0) by (t32 AG1 RCNT).
  assert (JC1: L5.img_clear M1 65536 393472). { eapply L5PK.img_clear_agree. apply AG1; alia. exact IC1. }
  assert (JC2: L5.img_clear M1 393512 393544). { eapply L5PK.img_clear_agree. apply AG1; alia. exact IC2. }
  assert (JC3: L5.img_clear M1 393560 393568). { eapply L5PK.img_clear_agree. apply AG1; alia. exact IC3. }
  assert (WCA1: L5.writable RSEGS M1 459768 8) by (eapply L5.writable_grows; [exact GR1 | exact WCA]).
  clear AG1 FR1 MS1.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unshelve epose proof (e3e1u_conc fx1 R1 M1 (S - 1008) obj ref obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx2 & R2 & M2 & MS2 & K2 & R2_1 & R2_2 & R2_8 & R2_10 & R2_11 & R2_12 & R2_13 & C48 & C40 & Cr16 & Cobj & C120 & C576 & C72 & C24 & C16 & C8 & C32 & C80 & C104 & FR2 & GR2).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }

  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  assert (AG2: forall a k, (a + k <= (S - 112) \/ S <= a) -> (a + k <= obj - 120 \/ obj + 8 <= a) -> (a + k <= ref + 16 \/ ref + 20 <= a) -> (a + k <= 459768 \/ 459776 <= a) ->
                0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M1 M2 a k).
  { intros a k E1 E2 E3 E4 Ha Hk i Hi. apply FR2; rewrite L5.unsigned_lit by alia; alia. }
  assert (DEF2: L5.defined M2 (S - 8336) 8336) by (eapply L5.defined_grows; [exact GR2 | exact DEF1]).
  assert (DEFo2: L5.defined M2 (obj - 128) 144) by (eapply L5.defined_grows; [exact GR2 | exact DEFo1]).
  assert (HH2: hi_heap HI ((ref, 66) :: (obj - 128, 144) :: LB) cr M2 (m_vmmaps model)).
  { eapply hi_heap_clientx. exact HH1. alia. 2: exact GR2. intros a Ha.
    destruct (Z_lt_le_dec a 459768) as [L0|G0]. 2: destruct (Z_lt_le_dec a 459776) as [L0'|G0']. 2: { right; right; right. unfold statx, EH_CAUGHT. alia. }
    all: destruct (Z_lt_le_dec a (obj - 120)) as [L2|G2]; [| destruct (Z_lt_le_dec a (obj + 8)) as [L2'|G2']; [right; right; left; exists (obj - 128, 144); split; [right; left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a (ref + 16)) as [L5|G5]; [| destruct (Z_lt_le_dec a (ref + 20)) as [L5'|G5']; [right; right; left; exists (ref, 66); split; [left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a ((S - 112))) as [L3|G3]; [left; apply FR2; rewrite L5.unsigned_lit by alia; alia|].
    all: destruct (Z_lt_le_dec a (S)) as [L4|G4]; [right; left; alia| left; apply FR2; rewrite L5.unsigned_lit by alia; alia]. }
  assert (HQ2: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M2).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S 8336 _ M M1 M2 [((S - 112), 112); (obj + -120, 128); (ref + 16, 4); (0 + 459768, 8)]). exact LBWF. alia. exact HQ1.
    { intros x Hx. apply FR2; intros Hin.
      - apply (Hx ((S - 112), 112)). left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (obj + -120, 128)). right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (ref + 16, 4)). right; right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (0 + 459768, 8)). right; right; right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
    exact GR2.
    constructor. apply L5PK.wr_scratch; alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. eapply L5PK.wr_fresh. exact FRR. alia. alia.
    constructor. eapply L5PK.wr_declared. left; reflexivity. alia. alia.
    constructor. }
  assert (R2_3: getr R2 (reg 3) = Z_to_bv 64 67584) by (kin K2 3%nat; exact R1_3).
  assert (R2_4: getr R2 (reg 4) = Z_to_bv 64 462648) by (kin K2 4%nat; exact R1_4).
  rewrite R1_9 in C24. rewrite R1_8 in C16.
  replace (S - 1008 + 960) with (S - 48) in C48 by lia. replace (S - 1008 + 968) with (S - 40) in C40 by lia. replace (S - 1008 + 984) with (S - 24) in C24 by lia.
  replace (S - 1008 + 992) with (S - 16) in C16 by lia. replace (S - 1008 + 1000) with (S - 8) in C8 by lia.
  pose proof (L5USU.u32_at_agree M1 M2 459776 0 ltac:(apply AG2; alia) ltac:(alia) ltac:(alia) ltac:(rewrite Z.add_0_l in B584; exact B584)) as U2.
  assert (JD1: L5.img_clear M2 65536 393472). { eapply L5PK.img_clear_agree. apply AG2; alia. exact JC1. }
  assert (JD2: L5.img_clear M2 393512 393544). { eapply L5PK.img_clear_agree. apply AG2; alia. exact JC2. }
  assert (JD3: L5.img_clear M2 393560 393568). { eapply L5PK.img_clear_agree. apply AG2; alia. exact JC3. }
  clear AG2 FR2 MS2.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx2 R2 M2 model ((ref, 66) :: (obj - 128, 144) :: LB) cr ref 66 K) as HF.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HF.
  apply HF; clear HF.
  - exact HH2.
  - exact Mh. - exact Ml. - exact Mm.
  - left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R2_10.
  - rewrite L5CoreKit.L5K.rl4. exact R2_4.
  - rewrite L5CoreKit.L5K.rl1, R2_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
  - unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R2_2, L5.unsigned_lit by alia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-3) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. alia. split. alia. split. alia.
    intros d m0 Hd Hm. assert (W2: L5.writable RSEGS M2 (S - 8336) 8336). { apply (L5C.writable_of_defined RSEGS). exact DEF2. alia. alia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 8336 + (a - (S - 8336))) by ring end. apply W2; alia.
  - exact HK0.
  - intros R3 M3 model3 RP3 [PRES3 _] MBV3 HH3.
    rewrite L5CoreKit.L5K.rl1, R2_1.
    cbn [lb_remove fst] in PRES3, HH3. rewrite Z.eqb_refl in PRES3, HH3.
    rewrite L5CoreKit.L5K.rl2, R2_2, L5.unsigned_lit in PRES3 by alia.
    match type of PRES3 with heap_pres_core _ _ ?x _ _ => replace x with (S - 48) in PRES3 by lia end.
    pose proof (hpres_of_core L ((obj - 128, 144) :: LB) ((S - 48)) M2 M3 PRES3) as HP3. rewrite (ly_stack L LY) in HP3. unfold HEAP_STACK in HP3.
    assert (AG3: forall a k, (S - 48) <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M2 M3 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP3. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    assert (AGo3: L5C.agree_on M2 M3 (obj - 128) 144).
    { eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP3. left; reflexivity. alia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT3: forall a, stat_rd (2 ^ 47) a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { apply (stat_keep_hpres (2 ^ 47) ((obj - 128, 144) :: LB) ((S - 48)) 8224 [] M2 M3 HP3). alia. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    Ltac s64 ST H := eapply (L5C.u64_at_agree RSEGS); [intros i Hi; apply ST; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP; alia | alia | alia | exact H].
    Ltac s32 ST H := eapply L5USU.u32_at_agree; [intros i Hi; apply ST; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP; alia | alia | alia | exact H].
    Ltac simg ST H := intros i Hi; rewrite (ST i) by (unfold stat_rd; alia); apply H; exact Hi.
    assert (C576_3: L5.u64_at RSEGS M3 (0 + 459768) 0) by (s64 STAT3 C576).
    assert (U3: L5.u32_at RSEGS M3 459776 0) by (s32 STAT3 U2).
    assert (JE1: L5.img_clear M3 65536 393472) by (simg STAT3 JD1).
    assert (JE2: L5.img_clear M3 393512 393544) by (simg STAT3 JD2).
    assert (JE3: L5.img_clear M3 393560 393568) by (simg STAT3 JD3).
    assert (DEF3: L5.defined M3 (S - 8336) 8336).
    { eapply (defined_across ((obj - 128, 144) :: LB) ((S - 48)) 8224 [] M2 M3). exact HP3. alia. alia. alia. alia. exact DEF2. }
    assert (DEFo3: L5.defined M3 (obj - 128) 144) by (eapply (L5C.defined_agree M2 M3); [exact AGo3 | exact DEFo2]).
    assert (MOK3: model_ok model3).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV3); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV3); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV3); exact Y3]]. }
    pose proof MOK3 as (Mh3 & Ml3 & Mm3).
    assert (R3i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg i) = getr R2 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R2 R3 i RP3). exact Hi. }
    assert (R3_2: getr R3 (reg 2) = Z_to_bv 64 ((S - 48))) by (rewrite (R3i 2%nat) by inl; rewrite R2_2; f_equal; lia).
    assert (R3_3: getr R3 (reg 3) = Z_to_bv 64 67584) by (rewrite (R3i 3%nat) by inl; exact R2_3).
    assert (R3_4: getr R3 (reg 4) = Z_to_bv 64 462648) by (rewrite (R3i 4%nat) by inl; exact R2_4).
    assert (R3_8: getr R3 (reg 8) = Z_to_bv 64 obj) by (rewrite (R3i 8%nat) by inl; exact R2_8).
    assert (R3_10: getr R3 (reg 10) = Z_to_bv 64 (U R3 10)) by (unfold U; symmetry; apply lit_of_word).
    assert (T2: forall a v, (S - 48) <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hn Hu. eapply (L5C.u64_at_agree RSEGS M2 M3). apply AG3; alia. alia. alia. exact Hu. }
    pose proof (T2 ((S - 48)) _ ltac:(alia) ltac:(alia) C48) as E48. pose proof (T2 ((S - 40)) _ ltac:(alia) ltac:(alia) C40) as E40.
    pose proof (T2 ((S - 24)) _ ltac:(alia) ltac:(alia) C24) as E24. pose proof (T2 ((S - 16)) _ ltac:(alia) ltac:(alia) C16) as E16.
    pose proof (T2 ((S - 8)) _ ltac:(alia) ltac:(alia) C8) as E8.
    assert (HQ3: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M3).
    { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB ((obj - 128, 144) :: LB) S 8336 _ ((S - 48)) 8224 [] M M2 M3). exact LBWF.
      alia. alia. exact HQ2. exact HP3. apply L5PK.lb_sub_cons. alia. alia. alia. constructor. }
    clear STAT3 T2.
    (* [comment removed for export] *)
    assert (STEP4: exists (fx4 : FPState) R4 M4,
       msteps RSEGS (st fx2 R3 256696 M3) (st fx4 R4 312064 M4)
       /\ (forall i, In i [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg i) = getr R3 (reg i))
       /\ getr R4 (reg 1) = Z_to_bv 64 (260908)
       /\ getr R4 (reg 2) = Z_to_bv 64 (S - 32)
       /\ getr R4 (reg 8) = Z_to_bv 64 (obj - 128)
       /\ getr R4 (reg 10) = Z_to_bv 64 (obj - 128)
       /\ (forall x : word, ~ (S - 112 <= bv_unsigned x < S - 48) -> M4 x = M3 x)
       /\ mem_grows M3 M4).
    { destruct BR1 as [BLO|BHI].
      - idtac.
      (* [comment removed for export] *)
      unshelve epose proof (e3e2u_bl_conc fx2 R3 M3 (S - 1008) obj (U R3 10) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_10 & R4_11 & R4_12 & FR4 & GR4).
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }

        exists fx4, R4, M4. split. exact MS4.
        split. { intros i Hi. apply K4. apply L5KP.In_of_existsb. revert Hi; clear; intros Hi. cbn in Hi. decompose [or] Hi; subst; try reflexivity; contradiction. }
        split. exact R4_1. split. { rewrite R4_2. f_equal; lia. } split. exact R4_8. split. exact R4_10.
        split. { intros x Hx. apply FR4. alia. } exact GR4.
      - idtac.
      (* [comment removed for export] *)
      unshelve epose proof (e3e2u_bh_conc fx2 R3 M3 (S - 1008) obj (U R3 10) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_10 & R4_11 & R4_12 & R4_14 & FR4 & GR4).
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }

        exists fx4, R4, M4. split. exact MS4.
        split. { intros i Hi. apply K4. apply L5KP.In_of_existsb. revert Hi; clear; intros Hi. cbn in Hi. decompose [or] Hi; subst; try reflexivity; contradiction. }
        split. exact R4_1. split. { rewrite R4_2. f_equal; lia. } split. exact R4_8. split. exact R4_10.
        split. { intros x Hx. apply FR4. alia. } exact GR4. }
    destruct STEP4 as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_10 & FR4 & GR4).
    eapply (L5.cps_of_msteps RSEGS). exact Mh3. exact Ml3. exact MS4.
    assert (AG4: forall a k, (a + k <= (S - 112) \/ (S - 48) <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M3 M4 a k).
    { intros a k E1 Ha Hk i Hi. apply FR4; rewrite L5.unsigned_lit by alia; alia. }
    assert (DEF4: L5.defined M4 (S - 8336) 8336) by (eapply L5.defined_grows; [exact GR4 | exact DEF3]).
    assert (HH4: hi_heap HI ((obj - 128, 144) :: LB) cr M4 (m_vmmaps model3)).
    { eapply hi_heap_clientx. exact HH3. alia. 2: exact GR4. intros a Ha.
      destruct (Z_lt_le_dec a ((S - 112))) as [L3|G3]; [left; apply FR4; rewrite L5.unsigned_lit by alia; alia|].
      destruct (Z_lt_le_dec a ((S - 48))) as [L4|G4]; [right; left; alia| left; apply FR4; rewrite L5.unsigned_lit by alia; alia]. }
    assert (HQ4: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M4).
    { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S 8336 _ M M3 M4 [((S - 112), 64)]). exact LBWF. alia. exact HQ3.
      intros x Hx. apply FR4. intros Hin. apply (Hx ((S - 112), 64)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR4.
      constructor. apply L5PK.wr_scratch; alia. constructor. }
    assert (R4_3: getr R4 (reg 3) = Z_to_bv 64 67584) by (rewrite (K4 3%nat) by (cbn; tauto); exact R3_3).
    assert (R4_4: getr R4 (reg 4) = Z_to_bv 64 462648) by (rewrite (K4 4%nat) by (cbn; tauto); exact R3_4).
    Ltac a64 AG H := eapply (L5C.u64_at_agree RSEGS); [apply AG; alia | alia | alia | exact H].
    assert (F24: L5.u64_at RSEGS M4 ((S - 24)) (U R 9)) by (a64 AG4 E24).
    assert (F16: L5.u64_at RSEGS M4 ((S - 16)) (U R 8)) by (a64 AG4 E16).
    assert (F8: L5.u64_at RSEGS M4 ((S - 8)) 133720) by (a64 AG4 E8).
    assert (C576_4: L5.u64_at RSEGS M4 (0 + 459768) 0) by (a64 AG4 C576_3).
    assert (U4: L5.u32_at RSEGS M4 459776 0). { eapply L5USU.u32_at_agree. apply AG4; alia. alia. alia. exact U3. }
    assert (JF1: L5.img_clear M4 65536 393472). { eapply L5PK.img_clear_agree. apply AG4; alia. exact JE1. }
    assert (JF2: L5.img_clear M4 393512 393544). { eapply L5PK.img_clear_agree. apply AG4; alia. exact JE2. }
    assert (JF3: L5.img_clear M4 393560 393568). { eapply L5PK.img_clear_agree. apply AG4; alia. exact JE3. }
    clear AG4 FR4 MS4.
    (* [comment removed for export] *)
    pose proof (hio_free L SCFG HI HIok fx4 R4 M4 model3 ((obj - 128, 144) :: LB) cr (obj - 128) 144 K) as HF.
    rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HF.
    apply HF; clear HF.
    + exact HH4.
    + exact Mh3. + exact Ml3. + exact Mm3.
    + left; reflexivity.
    + rewrite L5CoreKit.L5K.rl10. exact R4_10.
    + rewrite L5CoreKit.L5K.rl4. exact R4_4.
    + rewrite L5CoreKit.L5K.rl1, R4_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
    + unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R4_2, L5.unsigned_lit by alia.
      split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-2) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
      unfold HEAP_STACK. split. alia. split. alia. split. alia.
      intros d m0 Hd Hm. assert (W4: L5.writable RSEGS M4 (S - 8336) 8336). { apply (L5C.writable_of_defined RSEGS). exact DEF4. alia. alia. }
      match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 8336 + (a - (S - 8336))) by ring end. apply W4; alia.
    + exact HK0.
    + intros R5 M5 model5 RP5 [PRES5 _] MBV5 HH5.
      rewrite L5CoreKit.L5K.rl1, R4_1.
      cbn [lb_remove fst] in PRES5, HH5. rewrite Z.eqb_refl in PRES5, HH5.
      rewrite L5CoreKit.L5K.rl2, R4_2, L5.unsigned_lit in PRES5 by alia.
      match type of PRES5 with heap_pres_core _ _ ?x _ _ => replace x with (S - 32) in PRES5 by lia end.
      pose proof (hpres_of_core L LB ((S - 32)) M4 M5 PRES5) as HP5. rewrite (ly_stack L LY) in HP5. unfold HEAP_STACK in HP5.
      assert (AG5: forall a k, (S - 32) <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M4 M5 a k).
      { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP5. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
      assert (STAT5: forall a, stat_rd (2 ^ 47) a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
      { apply (stat_keep_hpres (2 ^ 47) LB ((S - 32)) 8224 [] M4 M5 HP5). alia. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
      assert (C576_5: L5.u64_at RSEGS M5 (0 + 459768) 0) by (s64 STAT5 C576_4).
      assert (U5: L5.u32_at RSEGS M5 459776 0) by (s32 STAT5 U4).
      assert (JG1: L5.img_clear M5 65536 393472) by (simg STAT5 JF1).
      assert (JG2: L5.img_clear M5 393512 393544) by (simg STAT5 JF2).
      assert (JG3: L5.img_clear M5 393560 393568) by (simg STAT5 JF3).
      assert (DEF5: L5.defined M5 (S - 8336) 8336).
      { eapply (defined_across LB ((S - 32)) 8224 [] M4 M5). exact HP5. alia. alia. alia. alia. exact DEF4. }
      assert (MOK5: model_ok model5).
      { destruct MOK3 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV5); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV5); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV5); exact Y3]]. }
      pose proof MOK5 as (Mh5 & Ml5 & Mm5).
      assert (R5i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr R4 (reg i)).
      { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R4 R5 i RP5). exact Hi. }
      assert (R5_2: getr R5 (reg 2) = Z_to_bv 64 ((S - 32))) by (rewrite (R5i 2%nat) by inl; rewrite R4_2; f_equal; lia).
      assert (R5_3: getr R5 (reg 3) = Z_to_bv 64 67584) by (rewrite (R5i 3%nat) by inl; exact R4_3).
      assert (R5_4: getr R5 (reg 4) = Z_to_bv 64 462648) by (rewrite (R5i 4%nat) by inl; exact R4_4).
      assert (R5_10: getr R5 (reg 10) = Z_to_bv 64 (U R5 10)) by (unfold U; symmetry; apply lit_of_word).
      assert (T4: forall a v, (S - 32) <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M5 a v).
      { intros a v Ha Hn Hu. eapply (L5C.u64_at_agree RSEGS M4 M5). apply AG5; alia. alia. alia. exact Hu. }
      pose proof (T4 ((S - 24)) _ ltac:(alia) ltac:(alia) F24) as G24. pose proof (T4 ((S - 16)) _ ltac:(alia) ltac:(alia) F16) as G16.
      pose proof (T4 ((S - 8)) _ ltac:(alia) ltac:(alia) F8) as G8.
      assert (HQ5: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M5).
      { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB S 8336 _ ((S - 32)) 8224 [] M M4 M5). exact LBWF.
        alia. alia. exact HQ4. exact HP5. apply L5PK.lb_sub_refl. alia. alia. alia. constructor. }
      clear STAT5 T4.
      (* [comment removed for export] *)
    (* [comment removed for export] *)
    unshelve epose proof (e3e3u_conc fx4 R5 M5 (S - 1008) (U R5 10) (U R 8) (U R 9) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx6 & R6 & M6 & MS6 & K6 & R6_1 & R6_2 & R6_8 & R6_9 & R6_10 & R6_11 & FR6 & GR6).
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }
    { (* [comment removed for export] *) pr. }

      eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS6.
      assert (AG6: forall a k, (a + k <= (S - 96) \/ (S - 32) <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M5 M6 a k).
      { intros a k E1 Ha Hk i Hi. apply FR6; rewrite L5.unsigned_lit by alia; alia. }
      assert (HH6: hi_heap HI LB cr M6 (m_vmmaps model5)).
      { eapply hi_heap_clientx. exact HH5. alia. 2: exact GR6. intros a Ha.
        destruct (Z_lt_le_dec a ((S - 96))) as [L3|G3]; [left; apply FR6; rewrite L5.unsigned_lit by alia; alia|].
        destruct (Z_lt_le_dec a ((S - 32))) as [L4|G4]; [right; left; alia| left; apply FR6; rewrite L5.unsigned_lit by alia; alia]. }
      assert (HQ6: L5C.hpres L LB S 8336 [(459768, 8); (459776, 4)] M M6).
      { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S 8336 _ M M5 M6 [((S - 96), 64)]). exact LBWF. alia. exact HQ5.
        intros x Hx. apply FR6. intros Hin. apply (Hx ((S - 96), 64)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR6.
        constructor. apply L5PK.wr_scratch; alia. constructor. }
      (* [comment removed for export] *)
      specialize (KE fx6 R6 M6 model5). unfold cfg, L5USU.CATCH_RET, L5USU.CATCH_SCR, HEAP_STACK, EH_CAUGHT, EH_UNCAUGHT in KE. apply KE; clear KE.
      * apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|Hi]. { rewrite R6_2, H2. f_equal. lia. }
        destruct Hi as [<-|Hi]. { kin K6 3%nat. rewrite R5_3, H3. reflexivity. }
        destruct Hi as [<-|Hi]. { kin K6 4%nat. rewrite R5_4, H4. reflexivity. }
        destruct Hi as [<-|Hi]. { rewrite R6_8. unfold U. apply lit_of_word. }
        destruct Hi as [<-|Hi]. { rewrite R6_9. unfold U. apply lit_of_word. }
        assert (G: forall j, In j [18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg j) = getr R (reg j)).
        { intros j Hj.
          rewrite (K6 j) by (apply L5KP.In_of_existsb; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; subst; try reflexivity; contradiction).
          rewrite (R5i j) by (revert Hj; clear; intros Hj; cbn in Hj; cbn; tauto).
          rewrite (K4 j) by (revert Hj; clear; intros Hj; cbn in Hj; cbn; tauto).
          rewrite (R3i j) by (revert Hj; clear; intros Hj; cbn in Hj; cbn; tauto).
          rewrite (K2 j) by (apply L5KP.In_of_existsb; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; subst; try reflexivity; contradiction).
          rewrite (K1 j) by (apply L5KP.In_of_existsb; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; subst; try reflexivity; contradiction).
          reflexivity. }
        apply G. L5CoreKit.L5K.inlist Hi.
      * rewrite Z.add_0_l in C576_5. eapply (L5C.u64_at_agree RSEGS M5 M6). apply AG6; alia. alia. alia. exact C576_5.
      * eapply L5USU.u32_at_agree. apply AG6; alia. alia. alia. exact U5.
      * exact HQ6.
      * eapply L5C.model_but_vm_trans. exact MBV3. exact MBV5.
      * exact HH6.
Qed.
End WithHeap.
End SCFG_2.
End L5CA3U.
