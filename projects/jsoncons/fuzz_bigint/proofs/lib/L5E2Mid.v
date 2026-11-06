(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue BigModel
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2A L5E2Kit L5E2Mid2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2M.
Import L5CS L5PS L5STRK L5E2A L5E2K L5E2M2.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).

(* [comment removed for export] *)
Ltac kin K i := rewrite (K i) by (apply L5KP.In_of_existsb; reflexivity).
(* [comment removed for export] *)
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
  | |- L5.writable _ ?M ?a ?n => first [ eassumption
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
Let e2_mid2 := e2_mid2 L HI LY LYX HIok.

(* [comment removed for export] *)
Lemma e2_mid (fx7 : FPState) (R0 R7 : bvmap 5 word) (M M7 : word -> option byte) (model model5 : Model) (K : TSet)
      (LB : list (Z * Z)) (cr : credit) (S : Z) (gd fl : bool) (av uid rnd canary hw A fden : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 459832 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  credit_ok L (debit L cr 144) 37 ->
  (* [comment removed for export] *)
  getr R7 (reg 2) = Z_to_bv 64 (S - 352) -> getr R7 (reg 3) = Z_to_bv 64 67584 -> getr R7 (reg 4) = Z_to_bv 64 459832 ->
  getr R7 (reg 9) = Z_to_bv 64 (A + 128) -> getr R7 (reg 10) = Z_to_bv 64 (A + 128) -> getr R7 (reg 11) = Z_to_bv 64 77618 ->
  getr R7 (reg 18) = Z_to_bv 64 (S + 64) -> getr R7 (reg 19) = Z_to_bv 64 0 ->
  (* [comment removed for export] *)
  L5.defined M7 (S - 10240) 10240 -> L5.defined M7 A 144 ->
  frame2 R0 S fden M7 -> 0 <= fden < 256 -> Z.testbit fden 0 = false -> frame2_top R0 S M7 ->
  e1_statics M7 gd fl av uid rnd canary hw ->
  L5KP.zeros_at M7 A 144 ->
  (* [comment removed for export] *)
  hi_heap HI ((A, 144) :: LB) (debit L cr 144) M7 (m_vmmaps model5) -> model_ok model5 -> model_but_vm model model5 ->
  block_range L A 144 -> blocks_apart A 144 LB ->
  L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M7 ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' ->
      L5US.e2_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB cr S M' R' LB' cr' ->
      L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' L5US.TOP_PAD M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx7 R7 DIV_CTOR M7 model5) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR37 R7_2 R7_3 R7_4 R7_9 R7_10 R7_11 R7_18 R7_19 DEF7 DEFA7 F7 Hfden Hbit FT7 ES7 ZA7
         HH7 MOK5 MBV BR BA HQ7 KE.
  pose proof MOK5 as (Mh & Ml & Mm).
  pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1. unfold hl_ceil in BR4.
  assert (CSP16: (S - 352) mod 16 = 0). { replace (S - 352) with (S + (-22) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact BR2. }
  pose proof ES7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _ & _ & _ & _ & _ & IC1 & IC2 & IC3).
  unfold cfg, DIV_CTOR.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unshelve epose proof (e2c1_conc fx7 R7 M7 (S - 352) (A + 128) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx8 & R8 & M8 & MS8 & K8 & R8_1 & R8_2 & R8_8 & R8_9 & R8_10 & R8_18 & Q64 & Q56 & Qobj & Q40 & Q32 & Q24 & Q16 & Q8 & FR8 & GR8).
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

  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS8.
  (* [comment removed for export] *)
  assert (AG8: forall a k, (a + k <= S - 352 - 128 \/ S - 352 <= a) -> (a + k <= A + 128 \/ A + 136 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M7 M8 a k).
  { intros a k H1 H2 Ha Hk i Hi. apply FR8; rewrite BG.unsigned_lit by alia; alia. }
  assert (STAT8: forall a, stat_rd av a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. apply FR8; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (e1_statics_keep M7 M8 gd fl av uid rnd canary hw ES7 STAT8) as ES8.
  pose proof (frame2_agree R0 S fden M7 M8 ltac:(apply AG8; alia) ltac:(alia) ltac:(alia) F7) as F8.
  pose proof (frame2_top_agree R0 S M7 M8 ltac:(apply AG8; alia) ltac:(alia) ltac:(alia) FT7) as FT8.
  assert (DEF8: L5.defined M8 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR8 | exact DEF7]).
  assert (DEFA8: L5.defined M8 A 144) by (eapply L5.defined_grows; [exact GR8 | exact DEFA7]).
  assert (Z8: forall i, 0 <= i < 8 -> L5.u8_at RSEGS M8 (A + i) 0).
  { intros i Hi. eapply (L5C.u8_at_agree RSEGS M7 M8). apply AG8; alia. alia. alia. apply (u8_of_zeros M7 A 144 i ZA7). alia. }
  assert (Z48: forall i, 0 <= i < 12 -> L5.u8_at RSEGS M8 (A + 48 + i) 0).
  { intros i Hi. eapply (L5C.u8_at_agree RSEGS M7 M8). apply AG8; alia. alia. alia. replace (A + 48 + i) with (A + (48 + i)) by alia. apply (u8_of_zeros M7 A 144 (48 + i) ZA7). alia. }
  assert (HH8: hi_heap HI ((A, 144) :: LB) (debit L cr 144) M8 (m_vmmaps model5)).
  { eapply hi_heap_clientx. exact HH7. alia. 2: exact GR8. intros a Ha.
    destruct (Z_lt_le_dec a (A + 128)) as [L2|G2]; [| destruct (Z_lt_le_dec a (A + 136)) as [L2'|G2']; [right; right; left; exists (A, 144); split; [left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a (S - 352 - 128)) as [L3|G3]; [left; apply FR8; rewrite BG.unsigned_lit by alia; alia|].
    all: destruct (Z_lt_le_dec a (S - 352)) as [L4|G4]; [right; left; alia| left; apply FR8; rewrite BG.unsigned_lit by alia; alia]. }
  assert (HQ8: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M8).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M7 M8 [(S - 352 + -128, 128); (A + 128 + 0, 8)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ7.
    { intros x Hx. apply FR8; intros Hin.
      - apply (Hx (S - 352 + -128, 128)). left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (A + 128 + 0, 8)). right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
    exact GR8.
    assert (FRA: L5PK.fresh_rng L LB A 144). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. alia. exact BA. }
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. }
  assert (R8_3: getr R8 (reg 3) = Z_to_bv 64 67584) by (kin K8 3%nat; exact R7_3).
  assert (R8_4: getr R8 (reg 4) = Z_to_bv 64 459832) by (kin K8 4%nat; exact R7_4).
  rewrite R7_19, BG.unsigned_lit in Q40 by lia. rewrite R7_18, BG.unsigned_lit in Q32 by alia. rewrite R7_9, BG.unsigned_lit in Q24 by alia.
  (* [comment removed for export] *)
  pose proof (hio_malloc L SCFG HI HIok fx8 R8 M8 model5 ((A, 144) :: LB) (debit L cr 144) 37 K) as HMA.
  rewrite (ly_segs L LY), (ly_malloc L LY), (ly_tp L LY) in HMA.
  apply HMA; clear HMA.
  - exact HH8.
  - exact Mh. - exact Ml. - exact Mm.
  - rewrite L5CoreKit.L5K.rl10. exact R8_10.
  - lia.
  - exact CR37.
  - rewrite L5CoreKit.L5K.rl4. exact R8_4.
  - rewrite L5CoreKit.L5K.rl1, R8_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
  - unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R8_2, BG.unsigned_lit by alia.
    split. { replace (S - 352 - 64) with (S + (-26) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. alia. split. alia. split. alia.
    intros d m0 Hd Hm. assert (W8: L5.writable RSEGS M8 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF8. alia. alia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply W8; alia.
  - exact HK0.
  - intros R9 M9 model9 ref HR10 RP9 BRr BAr DEFr PRES9 MBV9 HH9.
    rewrite L5CoreKit.L5K.rl1, R8_1.
    pose proof PRES9 as PRES9'. rewrite L5CoreKit.L5K.rl2, R8_2, BG.unsigned_lit in PRES9' by alia.
    pose proof (hpres_of_core L ((A, 144) :: LB) (S - 352 - 64) M8 M9 PRES9') as HP9. rewrite (ly_stack L LY) in HP9. unfold HEAP_STACK in HP9.
    assert (AG9: forall a k, S - 352 - 64 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M8 M9 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP9. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    assert (AGA9: L5C.agree_on M8 M9 A 144).
    { eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP9. left; reflexivity. alia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT9: forall a, stat_rd av a -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
    { apply (stat_keep_hpres av ((A, 144) :: LB) (S - 352 - 64) 8224 [] M8 M9 HP9). alia. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    pose proof (e1_statics_keep M8 M9 gd fl av uid rnd canary hw ES8 STAT9) as ES9.
    assert (DEF9: L5.defined M9 (S - 10240) 10240).
    { eapply (defined_across ((A, 144) :: LB) (S - 352 - 64) 8224 [] M8 M9). exact HP9. alia. alia. alia. alia. exact DEF8. }
    assert (DEFA9: L5.defined M9 A 144) by (eapply (L5C.defined_agree M8 M9); [exact AGA9 | exact DEFA8]).
    assert (MOK9: model_ok model9).
    { destruct MOK5 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV9); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV9); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV9); exact Y3]]. }
    pose proof (frame2_agree R0 S fden M8 M9 ltac:(apply AG9; alia) ltac:(alia) ltac:(alia) F8) as F9.
    pose proof (frame2_top_agree R0 S M8 M9 ltac:(apply AG9; alia) ltac:(alia) ltac:(alia) FT8) as FT9.
    assert (R9i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg i) = getr R8 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R8 R9 i RP9). exact Hi. }
    assert (T8: forall a v, S - 352 - 64 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M8 a v -> L5.u64_at RSEGS M9 a v).
    { intros a v Ha Hn Hu. eapply (L5C.u64_at_agree RSEGS M8 M9). apply AG9; alia. alia. alia. exact Hu. }
    rewrite L5CoreKit.L5K.rl10 in HR10.
    eapply (e2_mid2 fx8 R0 R9 M M9 model model9 K LB cr S gd fl av uid rnd canary hw A ref fden (bv_unsigned (getr R7 (reg 8)))
              HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF).
    + rewrite (R9i 2%nat) by inl. exact R8_2.
    + rewrite (R9i 3%nat) by inl. exact R8_3.
    + rewrite (R9i 4%nat) by inl. exact R8_4.
    + rewrite (R9i 9%nat) by inl. exact R8_9.
    + exact HR10.
    + rewrite (R9i 18%nat) by inl. exact R8_18.
    + exact DEF9. + exact DEFA9. + exact DEFr.
    + exact F9. + exact Hfden. + exact Hbit. + exact FT9. + exact ES9.
    + apply wrange.
    + apply T8. alia. alia. exact Q56.
    + apply T8. alia. alia. exact Q64.
    + apply T8. alia. alia. exact Q8.
    + apply T8. alia. alia. exact Q16.
    + apply T8. alia. alia. exact Q24.
    + apply T8. alia. alia. exact Q32.
    + apply T8. alia. alia. exact Q40.
    + intros i Hi. eapply (L5C.u8_at_agree RSEGS M8 M9). eapply L5C.agree_on_sub. exact AGA9. alia. alia. alia. alia. apply Z8. exact Hi.
    + intros i Hi. eapply (L5C.u8_at_agree RSEGS M8 M9). eapply L5C.agree_on_sub. exact AGA9. alia. alia. alia. alia. apply Z48. exact Hi.
    + eapply (L5C.u64_at_agree RSEGS M8 M9). eapply L5C.agree_on_sub. exact AGA9. alia. alia. alia. alia. rewrite Z.add_0_r in Qobj. exact Qobj.
    + exact HH9.
    + exact MOK9.
    + eapply L5C.model_but_vm_trans. exact MBV. exact MBV9.
    + exact BR. + exact BA. + exact BRr. + exact BAr.
    + eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB ((A, 144) :: LB) S L5DS.SCR_OPMOD L5US.xs_foot (S - 352 - 64) 8224 [] M M8 M9). exact LBWF.
      unfold L5DS.SCR_OPMOD; alia. alia. exact HQ8. exact HP9. apply L5PK.lb_sub_cons. unfold L5DS.SCR_OPMOD; alia. alia. alia. constructor.
    + exact KE.
Qed.
End WithHeap.
End SCFG_2.
End L5E2M.
