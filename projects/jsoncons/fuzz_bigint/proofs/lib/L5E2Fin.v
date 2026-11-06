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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2A L5E2B L5E2Kit.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2F.
Import L5CS L5PS L5STRK L5E2A L5E2B L5E2K.
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

(* [comment removed for export] *)
Lemma e2_fin (fx11 : FPState) (R0 R11 : bvmap 5 word) (M M11 : word -> option byte) (model model11 : Model) (K : TSet)
      (LB : list (Z * Z)) (cr : credit) (S : Z) (gd fl : bool) (av uid rnd canary hw A ref fden : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 459832 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  (* [comment removed for export] *)
  getr R11 (reg 1) = Z_to_bv 64 PAD1 -> getr R11 (reg 2) = Z_to_bv 64 (S - 352) -> getr R11 (reg 3) = Z_to_bv 64 67584 ->
  getr R11 (reg 4) = Z_to_bv 64 459832 -> getr R11 (reg 10) = Z_to_bv 64 (A + 128 - 32) ->
  (* [comment removed for export] *)
  L5.defined M11 (S - 10240) 10240 -> L5.defined M11 A 144 -> L5.defined M11 ref 37 ->
  frame2 R0 S fden M11 -> 0 <= fden < 256 -> Z.testbit fden 0 = false -> frame2_top R0 S M11 ->
  L5US.statics_landed M11 gd av uid rnd canary hw ->
  L5US.exc2_at M11 (A + 128) ref S ->
  (* [comment removed for export] *)
  hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M11 (m_vmmaps model11) -> model_ok model11 -> model_but_vm model model11 ->
  block_range L A 144 -> blocks_apart A 144 LB -> block_range L ref 37 -> blocks_apart ref 37 ((A, 144) :: LB) ->
  L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M11 ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' ->
      L5US.e2_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB cr S M' R' LB' cr' ->
      L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' L5US.TOP_PAD M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx11 R11 PAD1 M11 model11) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF R11_1 R11_2 R11_3 R11_4 R11_10 DEF11 DEFA11 DEFr11 F11 Hfden Hbit FT11 ST11 E11
         HH11 MOK11 MBV BR BA RR BAr HQ11 KE.
  pose proof MOK11 as (Mh & Ml & Mm).
  pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). pose proof RR as (RR0 & RR1 & RR2 & RR3 & RR4).
  rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1, RR1. unfold hl_ceil in BR4, RR4.
  pose proof (BAr (A, 144) ltac:(left; reflexivity)) as RA. cbn [fst snd] in RA.
  assert (CSP16: (S - 352) mod 16 = 0). { replace (S - 352) with (S + (-22) * 16) by alia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { replace (A + 128) with (A + 8 * 16) by alia. rewrite Z_mod_plus_full. exact BR2. }
  pose proof ST11 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14.
  pose proof (auxv_cells M11 av uid rnd hw S18) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19).
  pose proof E11 as (HDR & VT & IMP & RS).
  pose proof HDR as (Z8 & RC & TI & DT & UH & TH & Z12 & HS & AR & LS & CT & AP & EC & CL & P1 & P2).
  unfold L5US.TI_RUNTIME_ERROR, L5US.DTOR_RUNTIME_ERROR, L5US.UNEXPECTED_H, L5US.TERMINATE_H, L5US.EXC_ACTION, L5US.EXC_LSDA, L5US.TOP_PAD,
         L5US.EXC_CLASS, L5US.UE_CLEANUP in RC, TI, DT, UH, TH, HS, AR, LS, CT, AP, EC, CL, P1, P2.
  pose proof F11 as (F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 & F144 & F152 & F184 & F48).
  pose proof FT11 as (F16 & F8). unfold DIV_RET in F56. unfold OPMOD1_RET in F8.
  unfold cfg, PAD1. unfold PAD1 in R11_1.
  (* [comment removed for export] *)
  unshelve epose proof (e2p1_conc fx11 R11 M11 (S - 352) (A + 128) fden _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx12 & R12 & M12 & MS12 & K12 & R12_2 & R12_8 & R12_10 & R12_11 & FR12 & GR12).
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
  { (* [comment removed for export] *) rewrite land254_bit0 by assumption. pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS12.
  (* [comment removed for export] *)
  assert (AG12: forall a k, (a + k <= S - 352 - 64 \/ S - 352 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M11 M12 a k).
  { intros a k H1 Ha Hk i Hi. apply FR12. rewrite BG.unsigned_lit by alia. alia. }
  assert (STAT12: forall a, stat_rd av a -> M12 (Z_to_bv 64 a) = M11 (Z_to_bv 64 a)).
  { intros a Ha. apply FR12. rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (statics_landed_keep M11 M12 gd av uid rnd canary hw ST11 STAT12) as ST12.
  pose proof (frame2_agree R0 S fden M11 M12 ltac:(apply AG12; alia) ltac:(alia) ltac:(alia) F11) as F12.
  pose proof (frame2_top_agree R0 S M11 M12 ltac:(apply AG12; alia) ltac:(alia) ltac:(alia) FT11) as FT12.
  pose proof (exc2_at_agree M11 M12 (A + 128) ref S ltac:(apply AG12; alia) ltac:(apply AG12; alia) ltac:(alia) ltac:(alia) ltac:(alia) ltac:(alia) E11) as E12.
  assert (DEF12: L5.defined M12 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR12 | exact DEF11]).
  assert (DEFA12: L5.defined M12 A 144) by (eapply L5.defined_grows; [exact GR12 | exact DEFA11]).
  assert (DEFr12: L5.defined M12 ref 37) by (eapply L5.defined_grows; [exact GR12 | exact DEFr11]).
  assert (HH12: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M12 (m_vmmaps model11)).
  { eapply hi_heap_clientx. exact HH11. alia. 2: exact GR12. intros a Ha.
    destruct (Z_lt_le_dec a (S - 352 - 64)) as [L1|G1]. left. apply FR12. rewrite BG.unsigned_lit by alia. alia.
    destruct (Z_lt_le_dec a (S - 352)) as [L2|G2]. right; left. alia. left. apply FR12. rewrite BG.unsigned_lit by alia. alia. }
  assert (HQ12: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M12).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M11 M12 [(S - 352 + -64, 64)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ11.
    intros x Hx. apply FR12. intros Hin. apply (Hx (S - 352 + -64, 64)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR12.
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia. constructor. }
  assert (R12_1: getr R12 (reg 1) = Z_to_bv 64 140224) by (kin K12 1%nat; exact R11_1).
  assert (R12_3: getr R12 (reg 3) = Z_to_bv 64 67584) by (kin K12 3%nat; exact R11_3).
  assert (R12_4: getr R12 (reg 4) = Z_to_bv 64 459832) by (kin K12 4%nat; exact R11_4).
  pose proof ST12 as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & _ & _ & _ & T18 & _ & _ & _ & _ & T23 & T24 & T25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14.
  pose proof (auxv_cells M12 av uid rnd hw T18) as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19).
  pose proof E12 as ((_ & _ & _ & _ & _ & _ & _ & HS12 & _ & _ & CT12 & _ & EC12 & _ & P1_12 & P2_12) & _ & _ & _).
  unfold L5US.TOP_PAD, L5US.EXC_CLASS in HS12, CT12, EC12, P1_12, P2_12.
  pose proof F12 as (G56 & G64 & G72 & G80 & G88 & G96 & G104 & G112 & G120 & G128 & G136 & G144 & G152 & G184 & G48). unfold DIV_RET in G56.
  clear AG12 STAT12 FR12 MS12 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19
        S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S18 S23 S24 S25 F56 F64 F72 F80 F88 F96 F104 F112 F120 F128 F136 F144 F152 F184 F48
        Z8 RC TI DT UH TH Z12 HS AR LS CT AP EC CL P1 P2 HDR VT IMP RS.
  (* [comment removed for export] *)
  unshelve epose proof (e2r1x_conc fx12 R12 M12 (S - 352) (A + 128) av canary uid rnd hw (U R0 9) (U R0 18) (U R0 19) (U R0 20) (U R0 21) (U R0 22) (U R0 23) (U R0 24) (U R0 25) (U R0 26) (U R0 27)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx13 & R13 & M13 & MS13 & K13 & R13_1 & R13_2 & R13_8 & R13_9 & R13_10 & R13_11 & R13_18 & R13_19 & R13_20 & R13_21 & R13_22 & R13_23 & R13_24 & R13_25 & R13_26 & R13_27 & FR13 & GR13).
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
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
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
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS13.
  (* [comment removed for export] *)
  assert (AG13: forall a k, (a + k <= S - 352 - 7936 \/ S - 352 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M12 M13 a k).
  { intros a k H1 Ha Hk i Hi. apply FR13. rewrite BG.unsigned_lit by alia. alia. }
  assert (STAT13: forall a, stat_rd av a -> M13 (Z_to_bv 64 a) = M12 (Z_to_bv 64 a)).
  { intros a Ha. apply FR13. rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (statics_landed_keep M12 M13 gd av uid rnd canary hw ST12 STAT13) as ST13.
  pose proof (frame2_agree R0 S fden M12 M13 ltac:(apply AG13; alia) ltac:(alia) ltac:(alia) F12) as F13.
  pose proof (frame2_top_agree R0 S M12 M13 ltac:(apply AG13; alia) ltac:(alia) ltac:(alia) FT12) as FT13.
  pose proof (exc2_at_agree M12 M13 (A + 128) ref S ltac:(apply AG13; alia) ltac:(apply AG13; alia) ltac:(alia) ltac:(alia) ltac:(alia) ltac:(alia) E12) as E13.
  assert (DEF13: L5.defined M13 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR13 | exact DEF12]).
  assert (DEFA13: L5.defined M13 A 144) by (eapply L5.defined_grows; [exact GR13 | exact DEFA12]).
  assert (DEFr13: L5.defined M13 ref 37) by (eapply L5.defined_grows; [exact GR13 | exact DEFr12]).
  assert (HH13: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M13 (m_vmmaps model11)).
  { eapply hi_heap_clientx. exact HH12. alia. 2: exact GR13. intros a Ha.
    destruct (Z_lt_le_dec a (S - 352 - 7936)) as [L1|G1]. left. apply FR13. rewrite BG.unsigned_lit by alia. alia.
    destruct (Z_lt_le_dec a (S - 352)) as [L2|G2]. right; left. alia. left. apply FR13. rewrite BG.unsigned_lit by alia. alia. }
  assert (HQ13: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M13).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M12 M13 [(S - 352 + -7936, 7936)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ12.
    intros x Hx. apply FR13. intros Hin. apply (Hx (S - 352 + -7936, 7936)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR13.
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia. constructor. }
  assert (R13_3: getr R13 (reg 3) = Z_to_bv 64 67584) by (kin K13 3%nat; exact R12_3).
  assert (R13_4: getr R13 (reg 4) = Z_to_bv 64 459832) by (kin K13 4%nat; exact R12_4).
  pose proof ST13 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U23 & U24 & U25).
  pose proof F13 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I48).
  clear AG13 STAT13 FR13 MS13 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17 Y18 Y19
        T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T18 T23 T24 T25 G56 G64 G72 G80 G88 G96 G104 G112 G120 G128 G136 G144 G152 G184 G48 HS12 CT12 EC12 P1_12 P2_12.
  (* [comment removed for export] *)
  unshelve epose proof (e2p2_conc fx13 R13 M13 (S - 352) (A + 128) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx14 & R14 & M14 & MS14 & K14 & R14_2 & R14_8 & R14_10 & R14_11 & FR14 & GR14).
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
  { (* [comment removed for export] *) change (Z.land 0 254) with 0. pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS14.
  (* [comment removed for export] *)
  assert (AG14: forall a k, (a + k <= S - 352 + 240 \/ S - 352 + 304 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M13 M14 a k).
  { intros a k H1 Ha Hk i Hi. apply FR14. rewrite BG.unsigned_lit by alia. alia. }
  assert (STAT14: forall a, stat_rd av a -> M14 (Z_to_bv 64 a) = M13 (Z_to_bv 64 a)).
  { intros a Ha. apply FR14. rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (statics_landed_keep M13 M14 gd av uid rnd canary hw ST13 STAT14) as ST14.
  pose proof (frame2_top_agree R0 S M13 M14 ltac:(apply AG14; alia) ltac:(alia) ltac:(alia) FT13) as FT14.
  pose proof (exc2_at_agree M13 M14 (A + 128) ref S ltac:(apply AG14; alia) ltac:(apply AG14; alia) ltac:(alia) ltac:(alia) ltac:(alia) ltac:(alia) E13) as E14.
  assert (DEF14: L5.defined M14 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR14 | exact DEF13]).
  assert (DEFA14: L5.defined M14 A 144) by (eapply L5.defined_grows; [exact GR14 | exact DEFA13]).
  assert (DEFr14: L5.defined M14 ref 37) by (eapply L5.defined_grows; [exact GR14 | exact DEFr13]).
  assert (HH14: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M14 (m_vmmaps model11)).
  { eapply hi_heap_clientx. exact HH13. alia. 2: exact GR14. intros a Ha.
    destruct (Z_lt_le_dec a (S - 352 + 240)) as [L1|G1]. left. apply FR14. rewrite BG.unsigned_lit by alia. alia.
    destruct (Z_lt_le_dec a (S - 352 + 304)) as [L2|G2]. right; left. alia. left. apply FR14. rewrite BG.unsigned_lit by alia. alia. }
  assert (HQ14: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M14).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M13 M14 [(S - 352 + 240, 64)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ13.
    intros x Hx. apply FR14. intros Hin. apply (Hx (S - 352 + 240, 64)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR14.
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia. constructor. }
  assert (R14_1: getr R14 (reg 1) = Z_to_bv 64 138580) by (kin K14 1%nat; exact R13_1).
  assert (R14_3: getr R14 (reg 3) = Z_to_bv 64 67584) by (kin K14 3%nat; exact R13_3).
  assert (R14_4: getr R14 (reg 4) = Z_to_bv 64 459832) by (kin K14 4%nat; exact R13_4).
  pose proof ST14 as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & _ & _ & _ & V18 & _ & _ & _ & _ & V23 & V24 & V25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14.
  pose proof (auxv_cells M14 av uid rnd hw V18) as (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17 & W18 & W19).
  pose proof E14 as ((_ & _ & _ & _ & _ & _ & _ & HS14 & _ & _ & CT14 & _ & EC14 & _ & P1_14 & P2_14) & _ & _ & _).
  unfold L5US.TOP_PAD, L5US.EXC_CLASS in HS14, CT14, EC14, P1_14, P2_14.
  pose proof FT14 as (J16 & J8). unfold OPMOD1_RET in J8.
  clear AG14 STAT14 FR14 MS14 U23 U24 U25 I48.
  (* [comment removed for export] *)
  unshelve epose proof (e2r2x_conc fx14 R14 M14 (S - 352) (A + 128) av canary uid rnd hw (U R0 8)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx15 & R15 & M15 & MS15 & K15 & R15_1 & R15_2 & R15_8 & R15_10 & R15_11 & FR15 & GR15).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. } { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS15.
  (* [comment removed for export] *)
  assert (AG15: forall a k, (a + k <= S - 352 - 7936 \/ S - 352 + 304 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M14 M15 a k).
  { intros a k H1 Ha Hk i Hi. apply FR15. rewrite BG.unsigned_lit by alia. alia. }
  assert (STAT15: forall a, stat_rd av a -> M15 (Z_to_bv 64 a) = M14 (Z_to_bv 64 a)).
  { intros a Ha. apply FR15. rewrite BG.unsigned_lit; unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha; alia. }
  pose proof (statics_landed_keep M14 M15 gd av uid rnd canary hw ST14 STAT15) as ST15.
  pose proof (exc2_at_agree M14 M15 (A + 128) ref S ltac:(apply AG15; alia) ltac:(apply AG15; alia) ltac:(alia) ltac:(alia) ltac:(alia) ltac:(alia) E14) as E15.
  assert (DEFA15: L5.defined M15 A 144) by (eapply L5.defined_grows; [exact GR15 | exact DEFA14]).
  assert (DEFr15: L5.defined M15 ref 37) by (eapply L5.defined_grows; [exact GR15 | exact DEFr14]).
  assert (HH15: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M15 (m_vmmaps model11)).
  { eapply hi_heap_clientx. exact HH14. alia. 2: exact GR15. intros a Ha.
    destruct (Z_lt_le_dec a (S - 352 - 7936)) as [L1|G1]. left. apply FR15. rewrite BG.unsigned_lit by alia. alia.
    destruct (Z_lt_le_dec a (S - 352 + 304)) as [L2|G2]. right; left. alia. left. apply FR15. rewrite BG.unsigned_lit by alia. alia. }
  assert (HQ15: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M15).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M14 M15 [(S - 352 + -7936, 8240)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ14.
    intros x Hx. apply FR15. intros Hin. apply (Hx (S - 352 + -7936, 8240)). left; reflexivity. unfold L5.in_rng; cbn. alia. exact GR15.
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia. constructor. }
  (* [comment removed for export] *)
  specialize (KE fx15 R15 M15 model11 ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37)).
  unfold cfg, L5US.TOP_PAD in KE. apply KE; clear KE.
  - (* [comment removed for export] *)
    apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
    destruct Hi as [<-|Hi]. { rewrite R15_2, H02. f_equal. alia. }
    destruct Hi as [<-|Hi]. { kin K15 3%nat. rewrite R14_3, H03. reflexivity. }
    destruct Hi as [<-|Hi]. { kin K15 4%nat. rewrite R14_4, H04. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite R15_8. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 9%nat. kin K14 9%nat. rewrite R13_9. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 18%nat. kin K14 18%nat. rewrite R13_18. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 19%nat. kin K14 19%nat. rewrite R13_19. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 20%nat. kin K14 20%nat. rewrite R13_20. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 21%nat. kin K14 21%nat. rewrite R13_21. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 22%nat. kin K14 22%nat. rewrite R13_22. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 23%nat. kin K14 23%nat. rewrite R13_23. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 24%nat. kin K14 24%nat. rewrite R13_24. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 25%nat. kin K14 25%nat. rewrite R13_25. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 26%nat. kin K14 26%nat. rewrite R13_26. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { kin K15 27%nat. kin K14 27%nat. rewrite R13_27. apply lit_of_word. }
    destruct Hi.
  - (* [comment removed for export] *)
    unfold L5US.e2_landed, L5US.REF2_SZ, L5US.EXC23_SZ. exists (A + 128), ref. cbn [L5US.xs_gd L5US.xs_av L5US.xs_uid L5US.xs_rnd L5US.xs_canary L5US.xs_hw L5US.xs_of].
    replace (A + 128 - 128) with A by alia.
    split. { rewrite L5CoreKit.L5K.rl10. exact R15_10. }
    split. { rewrite L5CoreKit.L5K.rl11. exact R15_11. }
    split. { rewrite L5CoreKit.L5K.rl2, R15_2. f_equal. alia. }
    split. reflexivity.
    split. { split. exact BR. split. exact BA. exact DEFA15. }
    split. { split. exact RR. split. exact BAr. exact DEFr15. }
    split. { unfold L5US.exc_blocks_ok. replace (A + 128 - 128) with A by alia.
             assert (HA1: L5.hull_apart RSEGS A 144) by (apply hull_apart_of; exact BR1).
             assert (HA2: L5.hull_apart RSEGS ref 37) by (apply hull_apart_of; exact RR1).
             repeat split; first [assumption | alia]. }
    split. exact E15.
    split. exact ST15.
    unfold credit_le. alia.
  - exact HQ15.
  - exact MBV.
  - exact HH15.
Qed.
End WithHeap.
End SCFG_2.
End L5E2F.
