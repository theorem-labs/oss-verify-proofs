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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2A L5E2Kit L5E2Throw.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2M2.
Import L5CS L5PS L5STRK L5E2A L5E2K L5E2T.
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
Let e2_throw := e2_throw L HI LY LYX HIok.

(* [comment removed for export] *)
Lemma e2_mid2 (fx9 : FPState) (R0 R9 : bvmap 5 word) (M M9 : word -> option byte) (model model9 : Model) (K : TSet)
      (LB : list (Z * Z)) (cr : credit) (S : Z) (gd fl : bool) (av uid rnd canary hw A ref fden cv16 : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 459832 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  (* [comment removed for export] *)
  getr R9 (reg 2) = Z_to_bv 64 (S - 352 - 64) -> getr R9 (reg 3) = Z_to_bv 64 67584 -> getr R9 (reg 4) = Z_to_bv 64 459832 ->
  getr R9 (reg 9) = Z_to_bv 64 77618 -> getr R9 (reg 10) = Z_to_bv 64 ref -> getr R9 (reg 18) = Z_to_bv 64 12 ->
  (* [comment removed for export] *)
  L5.defined M9 (S - 10240) 10240 -> L5.defined M9 A 144 -> L5.defined M9 ref 37 ->
  frame2 R0 S fden M9 -> 0 <= fden < 256 -> Z.testbit fden 0 = false -> frame2_top R0 S M9 ->
  e1_statics M9 gd fl av uid rnd canary hw ->
  0 <= cv16 < 2 ^ 64 ->
  L5.u64_at RSEGS M9 (S - 352 - 56) 263612 -> L5.u64_at RSEGS M9 (S - 352 - 64) (A + 128) -> L5.u64_at RSEGS M9 (S - 352 - 8) 140136 ->
  L5.u64_at RSEGS M9 (S - 352 - 16) cv16 -> L5.u64_at RSEGS M9 (S - 352 - 24) (A + 128) -> L5.u64_at RSEGS M9 (S - 352 - 32) (S + 64) ->
  L5.u64_at RSEGS M9 (S - 352 - 40) 0 ->
  (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M9 (A + i) 0) -> (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M9 (A + 48 + i) 0) ->
  L5.u64_at RSEGS M9 (A + 128) 385144 ->
  (* [comment removed for export] *)
  hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M9 (m_vmmaps model9) -> model_ok model9 -> model_but_vm model model9 ->
  block_range L A 144 -> blocks_apart A 144 LB -> block_range L ref 37 -> blocks_apart ref 37 ((A, 144) :: LB) ->
  L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M9 ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' ->
      L5US.e2_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB cr S M' R' LB' cr' ->
      L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' L5US.TOP_PAD M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx9 R9 MALLOC_RET M9 model9) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF R9_2 R9_3 R9_4 R9_9 R9_10 R9_18 DEF9 DEFA9 DEFr9 F9 Hfden Hbit FT9 ES9 Hcv
         Q56 Q64 Q8 Q16 Q24 Q32 Q40 Z8 Z48 VT9 HH9 MOK9 MBV BR BA RR BAr HQ9 KE.
  pose proof MOK9 as (Mh & Ml & Mm).
  pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). pose proof RR as (RR0 & RR1 & RR2 & RR3 & RR4).
  rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1, RR1. unfold hl_ceil in BR4, RR4.
  pose proof (BAr (A, 144) ltac:(left; reflexivity)) as RA. cbn [fst snd] in RA.
  assert (CSP16: (S - 352) mod 16 = 0). { replace (S - 352) with (S + (-22) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact BR2. }
  pose proof ES9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _ & _ & _ & _ & _ & IC1 & IC2 & IC3).
  unfold cfg, MALLOC_RET.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unshelve epose proof (e2c2_conc fx9 R9 M9 (S - 352) (A + 128) ref cv16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx10 & R10 & M10 & MS10 & K10 & R10_1 & R10_2 & R10_8 & R10_9 & R10_10 & R10_11 & R10_12 & R10_18 & R10_19 & C8 & C24 & C32 & C33 & C34 & C35 & C36 & C16 & Cr8 & Cr0 & FR10 & GR10).
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

  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS10.
  (* [comment removed for export] *)
  assert (AG10: forall a k, (a + k <= S - 352 - 128 \/ S - 352 - 64 <= a) -> (a + k <= A + 136 \/ A + 144 <= a) -> (a + k <= ref \/ ref + 37 <= a) ->
                 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M9 M10 a k).
  { intros a k H1 H2 H3 Ha Hk i Hi. apply FR10; rewrite BG.unsigned_lit by alia; alia. }
  assert (STAT10: forall a, stat_rd av a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha. apply FR10; rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (e1_statics_keep M9 M10 gd fl av uid rnd canary hw ES9 STAT10) as ES10.
  pose proof (frame2_agree R0 S fden M9 M10 ltac:(apply AG10; alia) ltac:(alia) ltac:(alia) F9) as F10.
  pose proof (frame2_top_agree R0 S M9 M10 ltac:(apply AG10; alia) ltac:(alia) ltac:(alia) FT9) as FT10.
  assert (DEF10: L5.defined M10 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR10 | exact DEF9]).
  assert (DEFA10: L5.defined M10 A 144) by (eapply L5.defined_grows; [exact GR10 | exact DEFA9]).
  assert (DEFr10: L5.defined M10 ref 37) by (eapply L5.defined_grows; [exact GR10 | exact DEFr9]).
  assert (R10_3: getr R10 (reg 3) = Z_to_bv 64 67584) by (kin K10 3%nat; exact R9_3).
  assert (R10_4: getr R10 (reg 4) = Z_to_bv 64 459832) by (kin K10 4%nat; exact R9_4).
  assert (EO10: exc2_obj M10 (A + 128) ref).
  { unfold exc2_obj. split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M9 M10). apply AG10; alia. alia. alia. replace (A + 128 - 128 + i) with (A + i) by alia. apply Z8. alia. }
    split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M9 M10). apply AG10; alia. alia. alia. replace (A + 128 - 80 + i) with (A + 48 + i) by alia. apply Z48. alia. }
    split. { unfold L5US.VT_RUNTIME_ERROR. eapply (L5C.u64_at_agree RSEGS M9 M10). apply AG10; alia. alia. alia. exact VT9. }
    split. exact C8.
    apply (refstring_of_cells M10 ref); try assumption; alia. }
  assert (HH10: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M10 (m_vmmaps model9)).
  { eapply hi_heap_clientx. exact HH9. alia. 2: exact GR10. intros a Ha.
    destruct (Z_lt_le_dec a ref) as [L0|G0]. 2: destruct (Z_lt_le_dec a (ref + 37)) as [L0'|G0']. 2: { right; right; left. exists (ref, 37); split; [left; reflexivity | cbn; alia]. }
    all: destruct (Z_lt_le_dec a (A + 136)) as [L2|G2]; [| destruct (Z_lt_le_dec a (A + 144)) as [L2'|G2']; [right; right; left; exists (A, 144); split; [right; left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a (S - 352 - 128)) as [L3|G3]; [left; apply FR10; rewrite BG.unsigned_lit by alia; alia|].
    all: destruct (Z_lt_le_dec a (S - 352 - 64)) as [L4|G4]; [right; left; alia| left; apply FR10; rewrite BG.unsigned_lit by alia; alia]. }
  assert (HQ10: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M10).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M9 M10
              [(S - 352 + -128, 64); (A + 128 + 8, 8); (ref + 0, 37)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ9.
    { intros x Hx. apply FR10; intros Hin.
      - apply (Hx (S - 352 + -128, 64)). left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (A + 128 + 8, 8)). right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (ref + 0, 37)). right; right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
    exact GR10.
    assert (FRA: L5PK.fresh_rng L LB A 144). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. alia. exact BA. }
    assert (FRR: L5PK.fresh_rng L LB ref 37). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact RR1. split. alia. intros b Hb. apply BAr. right. exact Hb. }
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. eapply L5PK.wr_fresh. exact FRR. alia. alia.
    constructor. }
  eapply (e2_throw fx10 R0 R10 M M10 model model9 K LB cr S gd fl av uid rnd canary hw A ref fden HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF
            R10_2 R10_3 R10_4 R10_9 R10_10 R10_11 R10_12 DEF10 DEFA10 DEFr10 F10 Hfden Hbit FT10 ES10 EO10 HH10 MOK9 MBV BR BA RR BAr HQ10 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E2M2.
