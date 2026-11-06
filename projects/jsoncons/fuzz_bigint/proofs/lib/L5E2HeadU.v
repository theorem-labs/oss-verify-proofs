(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue BigModel
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2AU L5E2KitU L5E2MidU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2HU.
Import L5CSU L5PSU L5STRKU L5E2AU L5E2KU L5E2MU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).

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
Let e2_mid := e2_mid L HI LY LYX HIok.

(* [comment removed for export] *)
Lemma e2_head (fx : FPState) (R0 R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB : list (Z * Z)) (cr : credit) (S : Z) (gd fl : bool) (av uid rnd canary hw fden : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 462648 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  credit_ok L cr 144 -> credit_ok L (debit L cr 144) 37 ->
  (* [comment removed for export] *)
  getr R (reg 2) = Z_to_bv 64 (S - 416) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 462648 ->
  getr R (reg 8) = Z_to_bv 64 (S + 64) -> getr R (reg 9) = Z_to_bv 64 (S - 64) -> getr R (reg 10) = Z_to_bv 64 16 ->
  getr R (reg 18) = Z_to_bv 64 (S + 64) -> getr R (reg 19) = Z_to_bv 64 fden ->
  (* [comment removed for export] *)
  L5.defined M (S - 10240) 10240 ->
  frame2 R0 S fden M -> 0 <= fden < 256 -> Z.testbit fden 0 = false -> frame2_top R0 S M ->
  e1_statics M gd fl av uid rnd canary hw ->
  (* [comment removed for export] *)
  hi_heap HI LB cr M (m_vmmaps model) -> model_ok model ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' ->
      L5USU.e2_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB cr S M' R' LB' cr' ->
      L5C.hpres L LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' L5USU.TOP_PAD M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx R ZERO_THROW M model) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR37 H2 H3 H4 H8 H9 H10 H18 H19 DEF Fr Hfden Hbit FT ES HH MOK KE.
  pose proof MOK as (Mh & Ml & Mm).
  assert (CSP16: (S - 416) mod 16 = 0). { replace (S - 416) with (S + (-26) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (FAKE16: (S - 416 - 272) mod 16 = 0). { replace (S - 416 - 272) with (S + (-43) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _ & _ & _ & _ & _ & IC1 & IC2 & IC3).
  assert (HQ: L5C.hpres L LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M). { apply L5PK.hpres_refl. unfold L5DSU.SCR_OPMOD. exact DEF. }
  unfold cfg, ZERO_THROW.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unshelve epose proof (e2a1u_conc fx R M (S - 416) (S - 416 - 272) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_10 & R4_11 & D48 & D40 & D24 & D16 & D8 & FR4 & GR4).
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
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS4.
  (* [comment removed for export] *)
  assert (AG4: forall a k, (a + k <= S - 416 - 112 \/ S - 416 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M M4 a k).
  { intros a k H1 Ha Hk i Hi. apply FR4; rewrite BG.unsigned_lit by alia; alia. }
  assert (STAT4: forall a, stat_rd av a -> M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply FR4; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (e1_statics_keep M M4 gd fl av uid rnd canary hw ES STAT4) as ES4.
  pose proof (frame2_agree R0 S fden M M4 ltac:(apply AG4; alia) ltac:(alia) ltac:(alia) Fr) as F4.
  pose proof (frame2_top_agree R0 S M M4 ltac:(apply AG4; alia) ltac:(alia) ltac:(alia) FT) as FT4.
  assert (DEF4: L5.defined M4 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR4 | exact DEF]).
  assert (HH4: hi_heap HI LB cr M4 (m_vmmaps model)).
  { eapply hi_heap_clientx. exact HH. alia. 2: exact GR4. intros a Ha.
    destruct (Z_lt_le_dec a (S - 416 - 112)) as [L3|G3]; [left; apply FR4; rewrite BG.unsigned_lit by alia; alia|].
    destruct (Z_lt_le_dec a (S - 416)) as [L4|G4]; [right; left; alia| left; apply FR4; rewrite BG.unsigned_lit by alia; alia]. }
  assert (HQ4: L5C.hpres L LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M4).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M M4 [(S - 416 + -112, 112)]). exact LBWF. unfold L5DSU.SCR_OPMOD; alia. exact HQ.
    intros x Hx. apply FR4. intros Hin. apply (Hx (S - 416 + -112, 112)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR4.
    constructor. apply L5PK.wr_scratch; unfold L5DSU.SCR_OPMOD; alia. constructor. }
  assert (R4_3: getr R4 (reg 3) = Z_to_bv 64 67584) by (kin K4 3%nat; exact H3).
  assert (R4_4: getr R4 (reg 4) = Z_to_bv 64 462648) by (kin K4 4%nat; exact H4).
  assert (R4_18: getr R4 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K4 18%nat; exact H18).
  rewrite H9, BG.unsigned_lit in D24 by alia. rewrite H8, BG.unsigned_lit in D16 by alia.
  (* [comment removed for export] *)
  pose proof (hio_aligned L SCFG HI HIok fx4 R4 M4 model LB cr 144 K) as HA. rewrite (ly_segs L LY), (ly_aligned L LY), (ly_tp L LY) in HA.
  apply HA; clear HA.
  - exact HH4.
  - exact Mh. - exact Ml. - exact Mm.
  - rewrite L5CoreKit.L5K.rl10. exact R4_10.
  - rewrite L5CoreKit.L5K.rl11. exact R4_11.
  - lia.
  - exact CR144.
  - rewrite L5CoreKit.L5K.rl4. exact R4_4.
  - rewrite L5CoreKit.L5K.rl1, R4_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. lia. reflexivity.
  - unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit by alia.
    split. { replace (S - 416 - 48) with (S + (-29) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. alia. split. alia. split. alia.
    intros d m0 Hd Hm. assert (W4: L5.writable RSEGS M4 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF4. alia. alia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply W4; alia.
  - exact HK0.
  - intros R5 M5 model5 A HA10 RP5 BR BA DEFA5h PRES5 MBV5 HH5.
    rewrite L5CoreKit.L5K.rl1, R4_1. assert (DEFA5: L5.defined M5 A 144) by exact DEFA5h. clear DEFA5h.
    pose proof PRES5 as PRES5'. rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit in PRES5' by alia.
    pose proof (hpres_of_core L LB (S - 416 - 48) M4 M5 PRES5') as HP5. rewrite (ly_stack L LY) in HP5. unfold HEAP_STACK in HP5.
    pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1. unfold hl_ceil in BR4.
    assert (OBJ16: (A + 128) mod 16 = 0). { replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact BR2. }
    assert (AG5: forall a k, S - 416 - 48 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M4 M5 a k).
    { intros a k Ha Hk. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP5. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT5: forall a, stat_rd av a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
    { apply (stat_keep_hpres av LB (S - 416 - 48) 8224 [] M4 M5 HP5). alia. alia. alia. alia. alia. intros i Hi. apply L5C.outside_nil. }
    pose proof (e1_statics_keep M4 M5 gd fl av uid rnd canary hw ES4 STAT5) as ES5.
    pose proof ES5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JC1 & JC2 & JC3).
    assert (DEF5: L5.defined M5 (S - 10240) 10240).
    { eapply (defined_across LB (S - 416 - 48) 8224 [] M4 M5). exact HP5. alia. alia. alia. alia. exact DEF4. }
    assert (MOK5: model_ok model5).
    { destruct MOK as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBV5); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBV5); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBV5); exact Y3]]. }
    pose proof MOK5 as (Mh5 & Ml5 & Mm5).
    pose proof (frame2_agree R0 S fden M4 M5 ltac:(apply AG5; alia) ltac:(alia) ltac:(alia) F4) as F5.
    pose proof (frame2_top_agree R0 S M4 M5 ltac:(apply AG5; alia) ltac:(alia) ltac:(alia) FT4) as FT5.
    assert (R5i: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr R4 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R4 R5 i RP5). exact Hi. }
    assert (R5_2: getr R5 (reg 2) = Z_to_bv 64 (S - 416 - 48)) by (rewrite (R5i 2%nat) by inl; exact R4_2).
    assert (R5_3: getr R5 (reg 3) = Z_to_bv 64 67584) by (rewrite (R5i 3%nat) by inl; exact R4_3).
    assert (R5_4: getr R5 (reg 4) = Z_to_bv 64 462648) by (rewrite (R5i 4%nat) by inl; exact R4_4).
    assert (R5_18: getr R5 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite (R5i 18%nat) by inl; exact R4_18).
    rewrite L5CoreKit.L5K.rl10 in HA10.
    assert (R5_10: getr R5 (reg 10) = Z_to_bv 64 (A + 128 - 128)). { rewrite HA10. f_equal. lia. }
    assert (T4: forall a v, S - 416 - 48 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M5 a v).
    { intros a v Ha Hn Hu. eapply (L5C.u64_at_agree RSEGS M4 M5). apply AG5; alia. alia. alia. exact Hu. }
    pose proof (T4 (S - 416 - 48) _ ltac:(alia) ltac:(alia) D48) as E48. pose proof (T4 (S - 416 - 40) _ ltac:(alia) ltac:(alia) D40) as E40.
    pose proof (T4 (S - 416 - 24) _ ltac:(alia) ltac:(alia) D24) as E24. pose proof (T4 (S - 416 - 16) _ ltac:(alia) ltac:(alia) D16) as E16.
    pose proof (T4 (S - 416 - 8) _ ltac:(alia) ltac:(alia) D8) as E8.
    clear D48 D40 D24 D16 D8 FR4 AG4 STAT4.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    unshelve epose proof (e2a2u_conc fx4 R5 M5 (S - 416) (A + 128) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_11 & ZA7 & FR7 & GR7).
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
    eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS7.
    (* [comment removed for export] *)
    assert (AG7: forall a k, (a + k <= S - 416 - 112 \/ S - 416 - 48 <= a) -> (a + k <= A \/ A + 144 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M5 M7 a k).
    { intros a k H1 Ha2 Ha Hk i Hi. apply FR7; rewrite BG.unsigned_lit by alia; alia. }
    assert (STAT7: forall a, stat_rd av a -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
    { intros a Ha. apply FR7; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
    pose proof (e1_statics_keep M5 M7 gd fl av uid rnd canary hw ES5 STAT7) as ES7.
    pose proof (frame2_agree R0 S fden M5 M7 ltac:(apply AG7; alia) ltac:(alia) ltac:(alia) F5) as F7.
    pose proof (frame2_top_agree R0 S M5 M7 ltac:(apply AG7; alia) ltac:(alia) ltac:(alia) FT5) as FT7.
    assert (DEF7: L5.defined M7 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR7 | exact DEF5]).
    assert (DEFA7: L5.defined M7 A 144) by (eapply L5.defined_grows; [exact GR7 | exact DEFA5]).
    assert (HH7: hi_heap HI ((A, 144) :: LB) (debit L cr 144) M7 (m_vmmaps model5)).
    { eapply hi_heap_clientx. exact HH5. alia. 2: exact GR7. intros a Ha.
      destruct (Z_lt_le_dec a A) as [L2|G2]; [| destruct (Z_lt_le_dec a (A + 144)) as [L2'|G2']; [right; right; left; exists (A, 144); split; [left; reflexivity| cbn; alia] |]].
      all: destruct (Z_lt_le_dec a (S - 416 - 112)) as [L3|G3]; [left; apply FR7; rewrite BG.unsigned_lit by alia; alia|].
      all: destruct (Z_lt_le_dec a (S - 416 - 48)) as [L4|G4]; [right; left; alia| left; apply FR7; rewrite BG.unsigned_lit by alia; alia]. }
    assert (HQ5: L5C.hpres L LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M5).
    { eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB LB S L5DSU.SCR_OPMOD L5USU.xs_foot (S - 416 - 48) 8224 [] M M4 M5). exact LBWF.
      unfold L5DSU.SCR_OPMOD; alia. alia. exact HQ4. exact HP5. apply L5PK.lb_sub_refl. unfold L5DSU.SCR_OPMOD; alia. alia. alia. constructor. }
    assert (HQ7: L5C.hpres L LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M7).
    { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DSU.SCR_OPMOD L5USU.xs_foot M M5 M7 [(S - 416 + -112, 64); (A + 128 + -128, 144)]). exact LBWF. unfold L5DSU.SCR_OPMOD; alia. exact HQ5.
      { intros x Hx. apply FR7; intros Hin.
        - apply (Hx (S - 416 + -112, 64)). left; reflexivity. unfold L5.in_rng; cbn. alia.
        - apply (Hx (A + 128 + -128, 144)). right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
      exact GR7.
      assert (FRA: L5PK.fresh_rng L LB A 144). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. alia. exact BA. }
      constructor. apply L5PK.wr_scratch; unfold L5DSU.SCR_OPMOD; alia.
      constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
      constructor. }
    assert (R7_3: getr R7 (reg 3) = Z_to_bv 64 67584) by (kin K7 3%nat; exact R5_3).
    assert (R7_4: getr R7 (reg 4) = Z_to_bv 64 462648) by (kin K7 4%nat; exact R5_4).
    assert (R7_18: getr R7 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K7 18%nat; exact R5_18).
    assert (R7_8': getr R7 (reg 8) = Z_to_bv 64 (S + 64)) by (rewrite R7_8; f_equal; lia).
    replace (A + 128 - 128) with A in ZA7 by lia.
    eapply (e2_mid fx7 R0 R7 M M7 model model5 K LB cr S gd fl av uid rnd canary hw A fden HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR37
              R7_2 R7_3 R7_4 R7_8' R7_9 R7_10 R7_11 R7_18 DEF7 DEFA7 F7 Hfden Hbit FT7 ES7 ZA7 HH7 MOK5).
    + eapply L5C.model_but_vm_trans. 2: exact MBV5. apply L5C.model_but_vm_refl.
    + exact BR. + exact BA. + exact HQ7. + exact KE.
Qed.

(* [comment removed for export] *)
Theorem e2_chain : L5USU.e2_chain_spec L HI.
Proof.
  intros fx R0 M0 R M model K LB cr S st ZT H01 H02 H03 H04 XS AVTOP HH MOK HK0 STK S240 CR144 CR37 KE.
  destruct st as [gd fl av uid rnd canary hw]. cbn [L5USU.xs_av] in AVTOP.
  unfold L5USU.xs_pre, L5USU.lib_statics_at in XS. cbn [L5USU.xs_gd L5USU.xs_fl L5USU.xs_av L5USU.xs_uid L5USU.xs_rnd L5USU.xs_canary L5USU.xs_hw] in XS.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold L5DSU.SCR_OPMOD in SLO, DEF.
  destruct ZT as (fden & v16 & v24 & Q2 & Q3 & Q4 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27
                  & C8 & C16 & C24 & C32 & C64 & C56 & C48 & C40 & C72 & C80 & C88 & C96 & C104 & C112 & C120 & C128 & C136 & C144 & C152 & C160 & C168
                  & C200 & Hfden & Hbit & C192 & C184 & C176 & C216 & C208 & HP0).
  rewrite L5CoreKit.L5K.rl1 in H01. rewrite L5CoreKit.L5K.rl2 in H02, Q2. rewrite L5CoreKit.L5K.rl3 in H03, Q3. rewrite L5CoreKit.L5K.rl4 in H04, Q4.
  rewrite L5CoreKit.L5K.rl8 in Q8. rewrite L5CoreKit.L5K.rl9 in Q9. rewrite L5CoreKit.L5K.rl10 in Q10.
  rewrite L5CoreKit.L5K.rl18 in Q18. rewrite L5CoreKit.L5K.rl19 in Q19.
  unfold L5USU.GP in H03. unfold TP in H04.
  eapply (e2_head fx R0 R M model K LB cr S gd fl av uid rnd canary hw fden HK0 H02 H03 H04 A16 SLO S240 STOP AVTOP).
  - eapply (L5PK.lb_wf_of_heap L). exact HIok. exact HH.
  - exact CR144. - exact CR37.
  - exact Q2. - rewrite Q3. exact H03. - rewrite Q4. exact H04.
  - exact Q8. - exact Q9. - exact Q10. - exact Q18. - exact Q19.
  - exact DEF.
  - unfold frame2, U, DIV_RET. unfold L5DSU.U in *. repeat split; assumption.
  - exact Hfden. - exact Hbit.
  - unfold frame2_top, U, OPMOD1_RET, OPEQ_RET. unfold L5DSU.U in *. split. exact C32. split. exact C24. split. exact C16.
    replace (Z_to_bv 5 1) with (reg 1) in C8 by reflexivity. rewrite H01 in C8. unfold L5DSU.OPMOD1_RET in C8. rewrite BG.unsigned_lit in C8 by lia. exact C8.
  - exact XS.
  - exact HH. - exact MOK.
  - exact KE.
Qed.
End WithHeap.
End SCFG_2.
End L5E2HU.
