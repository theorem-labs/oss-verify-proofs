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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2A L5E2B L5E2C L5E2Kit L5E2Fin.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E2T.
Import L5CS L5PS L5STRK L5E2A L5E2B L5E2C L5E2K L5E2F.
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
Let e2_fin := e2_fin L HI LY LYX HIok.

(* [comment removed for export] *)
Lemma e2_throw (fx10 : FPState) (R0 R10 : bvmap 5 word) (M M10 : word -> option byte) (model model9 : Model) (K : TSet)
      (LB : list (Z * Z)) (cr : credit) (S : Z) (gd fl : bool) (av uid rnd canary hw A ref fden : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 459832 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB ->
  (* [comment removed for export] *)
  getr R10 (reg 2) = Z_to_bv 64 (S - 352) -> getr R10 (reg 3) = Z_to_bv 64 67584 -> getr R10 (reg 4) = Z_to_bv 64 459832 ->
  getr R10 (reg 9) = Z_to_bv 64 (A + 128) -> getr R10 (reg 10) = Z_to_bv 64 (A + 128) ->
  getr R10 (reg 11) = Z_to_bv 64 385384 -> getr R10 (reg 12) = Z_to_bv 64 253816 ->
  (* [comment removed for export] *)
  L5.defined M10 (S - 10240) 10240 -> L5.defined M10 A 144 -> L5.defined M10 ref 37 ->
  frame2 R0 S fden M10 -> 0 <= fden < 256 -> Z.testbit fden 0 = false -> frame2_top R0 S M10 ->
  e1_statics M10 gd fl av uid rnd canary hw ->
  exc2_obj M10 (A + 128) ref ->
  (* [comment removed for export] *)
  hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M10 (m_vmmaps model9) -> model_ok model9 -> model_but_vm model model9 ->
  block_range L A 144 -> blocks_apart A 144 LB -> block_range L ref 37 -> blocks_apart ref 37 ((A, 144) :: LB) ->
  L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M10 ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' ->
      L5US.e2_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB cr S M' R' LB' cr' ->
      L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' L5US.TOP_PAD M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx10 R10 THROW2 M10 model9) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF R10_2 R10_3 R10_4 R10_9 R10_10 R10_11 R10_12 DEF10 DEFA10 DEFr10 F10 Hfden Hbit FT10 ES10 EO10
         HH10 MOK9 MBV BR BA RR BAr HQ10 KE.
  pose proof MOK9 as (Mh & Ml & Mm).
  pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4). pose proof RR as (RR0 & RR1 & RR2 & RR3 & RR4).
  rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BR1, RR1. unfold hl_ceil in BR4, RR4.
  pose proof (BAr (A, 144) ltac:(left; reflexivity)) as RA. cbn [fst snd] in RA.
  assert (CSP16: (S - 352) mod 16 = 0). { replace (S - 352) with (S + (-22) * 16) by alia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { replace (A + 128) with (A + 8 * 16) by alia. rewrite Z_mod_plus_full. exact BR2. }
  pose proof ES10 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S1, S2, S3, S4, S5, S6, S7, S8, S9.
  pose proof (auxv_cells M10 av uid rnd hw S13) as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19).
  pose proof F10 as (F56 & F64 & F72 & F80 & F88 & F96 & F104 & F112 & F120 & F128 & F136 & F144 & F152 & F184 & F48).
  pose proof FT10 as (F16 & F8). unfold DIV_RET in F56. unfold OPMOD1_RET in F8.
  assert (WUW: L5.writable RSEGS M10 459617 6). { apply (writable_img M10 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; alia. }
  assert (WUC: L5.writable RSEGS M10 456960 4). { apply (writable_img M10 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; alia. }
  unfold cfg, THROW2.
  (* [comment removed for export] *)
  assert (STEPT: exists (fx11 : FPState) R11 M11,
     msteps RSEGS (st fx10 R10 140156 M10) (st fx11 R11 140224 M11)
     /\ (forall i, In i KS_T0 -> getr R11 (reg i) = getr R10 (reg i))
     /\ getr R11 (reg 1) = Z_to_bv 64 (140224)
     /\ getr R11 (reg 2) = Z_to_bv 64 (S - 352)
     /\ getr R11 (reg 9) = Z_to_bv 64 (A + 128)
     /\ getr R11 (reg 10) = Z_to_bv 64 (A + 128 - 32)
     /\ getr R11 (reg 11) = Z_to_bv 64 (0)
     /\ getr R11 (reg 12) = Z_to_bv 64 (257624)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 8) (S - 352 + 352)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 40) (A + 128)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 48) (133016)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 56) (91560)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 64) (91699)
     /\ L5.u32_at RSEGS M11 ((A + 128) - 68) (1)
     /\ L5.u8_at RSEGS M11 ((0) + 459620) (0)
     /\ L5.u8_at RSEGS M11 ((0) + 459619) (1)
     /\ L5.u8_at RSEGS M11 ((0) + 459622) (0)
     /\ L5.u8_at RSEGS M11 ((0) + 459621) (1)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 16) (0)
     /\ L5.u8_at RSEGS M11 ((0) + 459618) (0)
     /\ L5.u8_at RSEGS M11 ((0) + 459617) (1)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 120) (1)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 24) (257624)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 32) (4849336966747728640)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 88) (142700)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 104) (253816)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 112) (385384)
     /\ L5.u64_at RSEGS M11 ((A + 128) - 96) (142968)
     /\ L5.u32_at RSEGS M11 ((0) + 456960) (1)
     /\ (forall x : word, ~ ((S - 352) + -7936 <= bv_unsigned x < (S - 352) + -7936 + (7936)) -> ~ ((A + 128) + -120 <= bv_unsigned x < (A + 128) + -120 + (40)) ->
           ~ ((A + 128) + -68 <= bv_unsigned x < (A + 128) + -68 + (68)) -> ~ ((0) + 456960 <= bv_unsigned x < (0) + 456960 + (4)) -> ~ ((0) + 459617 <= bv_unsigned x < (0) + 459617 + (6)) -> M11 x = M10 x)
     /\ mem_grows M10 M11).
  { destruct fl.
    - destruct S5 as (U0 & U1 & U2 & U3 & U4 & U5).
      (* [comment removed for export] *)
      unshelve epose proof (e2t_v1_conc fx10 R10 M10 (S - 352) (A + 128) av canary uid rnd hw (U R0 27) (U R0 26) (U R0 25) (U R0 24) (U R0 23) (U R0 22) (U R0 21) (U R0 20) (U R0 19) (U R0 18) (U R0 9) (S + 64) (U R0 8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx11 & R11 & M11 & MS11 & K11 & REST).
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

      exists fx11, R11, M11. split. exact MS11. split. intros i Hi. apply K11. revert Hi. clear. intros Hi. exact Hi.
      decompose [and] REST. repeat split; assumption.
    - destruct S5 as (U0 & U2 & U4).
      (* [comment removed for export] *)
      unshelve epose proof (e2t_v0_conc fx10 R10 M10 (S - 352) (A + 128) av canary uid rnd hw (U R0 27) (U R0 26) (U R0 25) (U R0 24) (U R0 23) (U R0 22) (U R0 21) (U R0 20) (U R0 19) (U R0 18) (U R0 9) (S + 64) (U R0 8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as (fx11 & R11 & M11 & MS11 & K11 & REST).
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

      exists fx11, R11, M11. split. exact MS11. split. exact K11. exact REST. }
  clear X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19.
  destruct STEPT as (fx11 & R11 & M11 & MS11 & K11 & R11_1 & R11_2 & R11_9 & R11_10 & R11_11 & R11_12 & T8 & T40 & T48 & T56 & T64 & T68 & V244 & V243 & V246 & V245
                     & T16 & V242 & V241 & T120 & T24 & T32 & T88 & T104 & T112 & T96 & VUC & FR11 & GR11).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS11.
  (* [comment removed for export] *)
  assert (AG11: forall a k, (a + k <= S - 352 - 7936 \/ S - 352 <= a) -> (a + k <= A + 8 \/ A + 48 <= a) -> (a + k <= A + 60 \/ A + 128 <= a) ->
                 (a + k <= 456960 \/ 456964 <= a) -> (a + k <= 459617 \/ 459623 <= a) -> 0 <= a -> a + k <= 2 ^ 64 -> L5C.agree_on M10 M11 a k).
  { intros a k H1 H2 H3 H4 H5 Ha Hk i Hi. apply FR11; rewrite BG.unsigned_lit by alia; alia. }
  assert (R11_3: getr R11 (reg 3) = Z_to_bv 64 67584) by (kin K11 3%nat; exact R10_3).
  assert (R11_4: getr R11 (reg 4) = Z_to_bv 64 459832) by (kin K11 4%nat; exact R10_4).
  pose proof (frame2_agree R0 S fden M10 M11 ltac:(apply AG11; alia) ltac:(alia) ltac:(alia) F10) as F11.
  pose proof (frame2_top_agree R0 S M10 M11 ltac:(apply AG11; alia) ltac:(alia) ltac:(alia) FT10) as FT11.
  assert (DEF11: L5.defined M11 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR11 | exact DEF10]).
  assert (DEFA11: L5.defined M11 A 144) by (eapply L5.defined_grows; [exact GR11 | exact DEFA10]).
  assert (DEFr11: L5.defined M11 ref 37) by (eapply L5.defined_grows; [exact GR11 | exact DEFr10]).
  (* [comment removed for export] *)
  assert (ST11: L5US.statics_landed M11 gd av uid rnd canary hw).
  { unfold L5US.statics_landed, EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP.
    Ltac c64 AG := eapply (L5C.u64_at_agree RSEGS); [apply AG; alia | alia | alia | eassumption].
    split. c64 AG11. split. rewrite Z.add_0_l in VUC; exact VUC.
    split. { eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. exact S3. }
    split. { eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. exact S4. }
    rewrite !Z.add_0_l in V241, V242, V243, V244, V245, V246.
    split. exact V241. split. exact V242. split. exact V243. split. exact V244. split. exact V245. split. exact V246.
    split. c64 AG11. split. c64 AG11. split. c64 AG11. split. c64 AG11.
    split. exact S10. split. exact S11. split. exact S12.
    split. { intros j Hj. eapply (L5C.u64_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. apply S13. exact Hj. }
    split. exact S14. split. exact S15. split. exact S16. split. exact S17.
    assert (AGI: L5C.agree_on M10 M11 65536 (390760 - 65536)) by (apply AG11; alia).
    split. { intros i Hi. rewrite (AGI i) by alia. apply S18. exact Hi. }
    split. { intros i Hi. rewrite (AGI i) by alia. apply S19. exact Hi. }
    intros i Hi. rewrite (AGI i) by alia. apply S20. exact Hi. }
  (* [comment removed for export] *)
  assert (E11: L5US.exc2_at M11 (A + 128) ref S).
  { destruct EO10 as (Z8 & Z12 & VT & IMP & RS).
    unfold L5US.exc2_at, L5US.exc_hdr, L5US.TI_RUNTIME_ERROR, L5US.DTOR_RUNTIME_ERROR, L5US.UNEXPECTED_H, L5US.TERMINATE_H, L5US.EXC_ACTION, L5US.EXC_LSDA,
           L5US.TOP_PAD, L5US.EXC_CLASS, L5US.UE_CLEANUP.
    split.
    - split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. apply Z8. exact Hi. }
      split. exact T120. split. exact T112. split. exact T104. split. exact T96. split. exact T88.
      split. { intros i Hi. eapply (L5C.u8_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. apply Z12. exact Hi. }
      split. exact T68. split. exact T64. split. exact T56. split. exact T48. split. exact T40. split. exact T32. split. exact T24. split. exact T16.
      replace (S - 352 + 352) with S in T8 by alia. exact T8.
    - split. { eapply (L5C.u64_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. exact VT. }
      split. { eapply (L5C.u64_at_agree RSEGS M10 M11). apply AG11; alia. alia. alia. exact IMP. }
      eapply L5US.refstring_at_agree; [| alia | | exact RS]; unfold L5US.zero_divide_msg; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [| alia].
      apply AG11; alia. }
  assert (HH11: hi_heap HI ((ref, 37) :: (A, 144) :: LB) (debit L (debit L cr 144) 37) M11 (m_vmmaps model9)).
  { eapply hi_heap_clientx. exact HH10. alia. 2: exact GR11. intros a Ha.
    destruct (Z_lt_le_dec a 456960) as [L0|G0]. 2: destruct (Z_lt_le_dec a 456964) as [L0'|G0']. 2: { right; right; right. unfold statx, EH_CAUGHT. alia. }
    all: destruct (Z_lt_le_dec a 459617) as [L1|G1]; [| destruct (Z_lt_le_dec a 459623) as [L1'|G1']; [right; right; right; unfold statx, UW_FLAGS; alia |]].
    all: destruct (Z_lt_le_dec a (A + 8)) as [L2|G2]; [| destruct (Z_lt_le_dec a (A + 128)) as [L2'|G2']; [right; right; left; exists (A, 144); split; [right; left; reflexivity| cbn; alia] |]].
    all: destruct (Z_lt_le_dec a (S - 352 - 7936)) as [L3|G3]; [left; apply FR11; rewrite BG.unsigned_lit by alia; alia|].
    all: destruct (Z_lt_le_dec a (S - 352)) as [L4|G4]; [right; left; alia| left; apply FR11; rewrite BG.unsigned_lit by alia; alia]. }
  assert (HQ11: L5C.hpres L LB S L5DS.SCR_OPMOD L5US.xs_foot M M11).
  { eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB S L5DS.SCR_OPMOD L5US.xs_foot M M10 M11
              [(S - 352 + -7936, 7936); (A + 128 + -120, 40); (A + 128 + -68, 68); (0 + 456960, 4); (0 + 459617, 6)]). exact LBWF. unfold L5DS.SCR_OPMOD; alia. exact HQ10.
    { intros x Hx. apply FR11; intros Hin.
      - apply (Hx (S - 352 + -7936, 7936)). left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (A + 128 + -120, 40)). right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (A + 128 + -68, 68)). right; right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (0 + 456960, 4)). right; right; right; left; reflexivity. unfold L5.in_rng; cbn. alia.
      - apply (Hx (0 + 459617, 6)). right; right; right; right; left; reflexivity. unfold L5.in_rng; cbn. alia. }
    exact GR11.
    assert (FRA: L5PK.fresh_rng L LB A 144). { split. alia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact BR1. split. alia. exact BA. }
    constructor. apply L5PK.wr_scratch; unfold L5DS.SCR_OPMOD; alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. eapply L5PK.wr_fresh. exact FRA. alia. alia.
    constructor. eapply L5PK.wr_declared. unfold L5US.xs_foot. left; reflexivity. unfold EH_UNCAUGHT; alia. unfold EH_UNCAUGHT; alia.
    constructor. eapply L5PK.wr_declared. unfold L5US.xs_foot. right; left; reflexivity. unfold UW_FLAGS; alia. unfold UW_FLAGS; alia.
    constructor. }
  eapply (e2_fin fx11 R0 R11 M M11 model model9 K LB cr S gd fl av uid rnd canary hw A ref fden HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF
            R11_1 R11_2 R11_3 R11_4 R11_10 DEF11 DEFA11 DEFr11 F11 Hfden Hbit FT11 ST11 E11 HH11 MOK9 MBV BR BA RR BAr HQ11 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E2T.
