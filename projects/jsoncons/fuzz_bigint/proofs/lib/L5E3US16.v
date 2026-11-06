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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore BigLinkBase BigLinkGlue BigModel
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3AU L5E3T0U L5E3T1U L5E3PU L5E3R1U L5E3R2U L5E3US17.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3US16.
Import L5CSU L5PSU L5STRKU L5E2KU L5E3AU L5E3T0U L5E3T1U L5E3PU L5E3R1U L5E3R2U.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)).

Ltac kin K i := rewrite (K i) by (apply L5KP.In_of_existsb; reflexivity).
Ltac regval := repeat match goal with |- context [bv_unsigned (getr ?R (Z_to_bv 5 (Z.of_nat ?j)))] =>
  match goal with H : getr R (Z_to_bv 5 (Z.of_nat j)) = Z_to_bv 64 _ |- _ => rewrite H, BG.unsigned_lit by alia0 end end.
Ltac pr :=
  try regval;
  lazymatch goal with
  | |- getr _ _ = _ => first [ eassumption | etransitivity; [eassumption|]; f_equal; ring ]
  | |- L5.u64_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u64_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5.u8_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u8_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end
        | match goal with H : forall i, 0 <= i < _ -> L5.u8_at _ M _ 0 |- _ =>
            lazymatch goal with |- L5.u8_at _ _ ?a0 _ => lazymatch type of H with forall i, _ -> L5.u8_at _ _ (?b + i) _ =>
              replace a0 with (b + (a0 - b)) by ring; apply H; alia0 end end end ]
  | |- L5.u32_at _ ?M ?a ?v => first [ eassumption | rewrite ?Z.add_0_l, ?Z.add_0_r; eassumption
        | match goal with H : L5.u32_at _ M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5KP.uw_at _ ?w ?M ?a ?v => first [ eassumption
        | match goal with H : L5KP.uw_at _ w M ?a' ?v' |- _ => replace a with a' by ring; replace v with v' by ring; exact H end ]
  | |- L5.defined ?M ?a ?n => first [ eassumption
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.defined_sub M a' n' a n H); alia0 end ]
  | |- L5.writable _ ?M ?a ?n => first [ eassumption | rewrite ?Z.add_0_l; eassumption
        | match goal with H : L5.defined M ?a' ?n' |- _ => apply (L5.writable_sub _ M a' n' a n); [apply (L5C.writable_of_defined _ M a' n' H); alia0 | alia0 | alia0] end ]
  | |- ?a mod ?m = 0 => first [ eassumption | match goal with H : ?b mod m = 0 |- _ => replace a with b by ring; exact H end ]
  | |- L5.img_clear _ _ _ => eassumption
  | |- 0 <= U _ _ < _ => unfold U; apply wrange
  | |- 0 <= bv_unsigned _ < _ => apply wrange
  | |- _ => first [ eassumption | alia1 ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Tactic Notation "kl" hyp_list(l) := clear - l; lia.
Lemma tr64 Mo Mn a v (P : Prop) : (P -> L5C.agree_on Mo Mn a 8 /\ 0 <= a /\ a + 8 <= 2 ^ 64) -> P -> L5.u64_at RSEGS Mo a v -> L5.u64_at RSEGS Mn a v.
Proof. intros AG HP H. destruct (AG HP) as (G & Ha & Hn). exact (L5C.u64_at_agree RSEGS Mo Mn a v G Ha Hn H). Qed.
Lemma tr32 Mo Mn a v (P : Prop) : (P -> L5C.agree_on Mo Mn a 4 /\ 0 <= a /\ a + 4 <= 2 ^ 64) -> P -> L5.u32_at RSEGS Mo a v -> L5.u32_at RSEGS Mn a v.
Proof. intros AG HP H. destruct (AG HP) as (G & Ha & Hn). exact (L5USU.u32_at_agree Mo Mn a v G Ha Hn H). Qed.
Lemma tr8 Mo Mn a v (P : Prop) : (P -> L5C.agree_on Mo Mn a 1 /\ 0 <= a /\ a + 1 <= 2 ^ 64) -> P -> L5.u8_at RSEGS Mo a v -> L5.u8_at RSEGS Mn a v.
Proof. intros AG HP H. destruct (AG HP) as (G & Ha & Hn). exact (L5C.u8_at_agree RSEGS Mo Mn a v G Ha Hn H). Qed.
Lemma trb64 Mo Mn b n a v : L5C.agree_on Mo Mn b n -> (b <= a /\ a + 8 <= b + n /\ 0 <= a /\ a + 8 <= 2 ^ 64) -> L5.u64_at RSEGS Mo a v -> L5.u64_at RSEGS Mn a v.
Proof. intros AG (H1 & H2 & Ha & Hn) H. exact (L5C.u64_at_agree RSEGS Mo Mn a v (L5C.agree_on_sub Mo Mn b n a 8 AG H1 H2) Ha Hn H). Qed.
Lemma trb32 Mo Mn b n a v : L5C.agree_on Mo Mn b n -> (b <= a /\ a + 4 <= b + n /\ 0 <= a /\ a + 4 <= 2 ^ 64) -> L5.u32_at RSEGS Mo a v -> L5.u32_at RSEGS Mn a v.
Proof. intros AG (H1 & H2 & Ha & Hn) H. exact (L5USU.u32_at_agree Mo Mn a v (L5C.agree_on_sub Mo Mn b n a 4 AG H1 H2) Ha Hn H). Qed.
Lemma trb8 Mo Mn b n a v : L5C.agree_on Mo Mn b n -> (b <= a /\ a + 1 <= b + n /\ 0 <= a /\ a + 1 <= 2 ^ 64) -> L5.u8_at RSEGS Mo a v -> L5.u8_at RSEGS Mn a v.
Proof. intros AG (H1 & H2 & Ha & Hn) H. exact (L5C.u8_at_agree RSEGS Mo Mn a v (L5C.agree_on_sub Mo Mn b n a 1 AG H1 H2) Ha Hn H). Qed.
(* [comment removed for export] *)
Lemma in_dec (lo hi a : Z) : {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a hi); [left; lia|] |]; right; lia. Qed.
Ltac cellfix H :=
  lazymatch goal with
  | |- ?f _ ?M ?a ?v => lazymatch type of H with _ _ _ ?a' ?v' => replace a with a' by ring; replace v with v' by ring; exact H end
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
Let XSF : list L5.range := [(459776, 4); (462433, 6)].
Let seg17 := L5E3US17.seg17 L HI LY LYX HIok.

Lemma seg16 (fx27 : FPState) (R0 R R28 : bvmap 5 word) (M M28 : word -> option byte) (model model28 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A ref : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 462648 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB1 ->
  credit_ok L cr 144 -> credit_ok L (debit L cr 144) 48 -> credit_ok L (debit L (debit L cr 144) 48) 66 ->
  0 <= fb808 < 256 -> Z.testbit fb808 0 = false ->
  0 <= fb744 < 256 -> Z.testbit fb744 0 = true ->
  0 <= fb712 < 256 -> Z.testbit fb712 0 = true ->
  0 <= fb664 < 256 -> Z.testbit fb664 0 = false ->
  0 <= fb528 < 256 -> Z.testbit fb528 0 = false ->
  0 <= fb472 < 256 -> Z.testbit fb472 0 = false ->
  0 <= fb344 < 256 -> Z.testbit fb344 0 = false ->
  0 <= fb280 < 256 -> Z.testbit fb280 0 = false ->
  0 <= fb248 < 256 -> Z.testbit fb248 0 = true ->
  0 <= fb200 < 256 -> Z.testbit fb200 0 = true ->
  0 <= fb64 < 256 -> Z.testbit fb64 0 = false ->
  0 <= w960 < 2 ^ 64 ->
  0 <= w976 < 2 ^ 64 ->
  0 <= w552 < 2 ^ 64 ->
  0 <= w568 < 2 ^ 64 ->
  0 <= w576 < 2 ^ 64 ->
  0 <= w584 < 2 ^ 64 ->
  0 <= w592 < 2 ^ 64 ->
  0 <= w600 < 2 ^ 64 ->
  0 <= w608 < 2 ^ 64 ->
  0 <= w616 < 2 ^ 64 ->
  0 <= w624 < 2 ^ 64 ->
  0 <= w632 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R28 (reg 2) = Z_to_bv 64 (S - 416) ->
  (* [comment removed for export] *) getr R28 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R28 (reg 4) = Z_to_bv 64 462648 ->
  (* [comment removed for export] *) getr R28 (reg 8) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R28 (reg 9) = Z_to_bv 64 (S - 64) ->
  (* [comment removed for export] *) getr R28 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R28 (reg 19) = Z_to_bv 64 w568 ->
  (* [comment removed for export] *) getr R28 (reg 20) = Z_to_bv 64 w576 ->
  (* [comment removed for export] *) getr R28 (reg 21) = Z_to_bv 64 w584 ->
  (* [comment removed for export] *) getr R28 (reg 22) = Z_to_bv 64 w592 ->
  (* [comment removed for export] *) getr R28 (reg 23) = Z_to_bv 64 w600 ->
  (* [comment removed for export] *) getr R28 (reg 24) = Z_to_bv 64 w608 ->
  (* [comment removed for export] *) getr R28 (reg 25) = Z_to_bv 64 w616 ->
  (* [comment removed for export] *) getr R28 (reg 26) = Z_to_bv 64 w624 ->
  (* [comment removed for export] *) getr R28 (reg 27) = Z_to_bv 64 w632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 72) 140436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 80) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 88) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 96) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 104) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 112) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 120) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 128) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 136) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 144) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 152) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 160) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 168) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 24) 134416 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 32) (S + 96) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 8) 133204 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (S - 344) fb344 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 224) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 232) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (S - 200) fb200 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 176) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (S - 184) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (S - 64) fb64 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M28 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M28 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 128) 376080 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M28 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M28 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 80) 133556 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 72) 91856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 64) 91995 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M28 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 104) 260436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 40) 145512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 24) 256628 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 16) 376040 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M28 (A + 32) 145780 ->
  (* [comment removed for export] *) L5USU.statics_landed M28 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M28 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M28 ref 66 ->
  (* [comment removed for export] *) L5.defined M28 A 144 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M28 (m_vmmaps model28) ->
  (* [comment removed for export] *) model_ok model28 ->
  (* [comment removed for export] *) model_but_vm model model28 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M28 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5USU.e3_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133556 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx27 R28 142628 M28 model28) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 R28_2 R28_3 R28_4 R28_8 R28_9 R28_18 R28_19 R28_20 R28_21 R28_22 R28_23 R28_24 R28_25 R28_26 R28_27 c28_Sm72 c28_Sm80 c28_Sm88 c28_Sm96 c28_Sm104 c28_Sm112 c28_Sm120 c28_Sm128 c28_Sm136 c28_Sm144 c28_Sm152 c28_Sm160 c28_Sm168 c28_Sm24 c28_Sm32 c28_Sm8 c28_Sm16 c28_Sm344w1 c28_Sm280w1 c28_Sm248w1 c28_Sm224 c28_Sm232 c28_Sm200w1 c28_Sm176 c28_Sm184 c28_Sm64w1 c28_Om128z8 c28_Om80z12 c28_Op0 c28_Op8 c28_Fp24 c28_Fp32 c28_Fp40 c28_Fp48 c28_Fp56 c28_Fp64w1 c28_Fp65w1 c28_Fp16w4 c28_Fp8 c28_Fp0 c28_Om8 c28_Om40 c28_Om48 c28_Om56 c28_Om64 c28_Om68w4 c28_Om16 c28_Om120 c28_Om24 c28_Om32 c28_Om88 c28_Om104 c28_Om112 c28_Om96 ES28 DEF28 DEFref_28 DEFA_28 BR_ref BR_A AP_ref_A FRSH_ref FRSH_A HH28 MOK28 MBV28 HQ28 KE.
  pose proof MOK28 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof ES28 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 1008) mod 16 = 0). { clear - A16. replace (S - 1008) with (S + (-63) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  set (u28_10 := U R28 10). assert (Wu28_10: 0 <= u28_10 < 2 ^ 64) by (unfold u28_10, U; apply wrange).
  assert (R28_10: getr R28 (reg 10) = Z_to_bv 64 u28_10) by (unfold u28_10, U; symmetry; apply lit_of_word). clearbody u28_10.
  pose proof ES28 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M28 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p5cu_conc fx27 R28 M28 (S - 1008) (A + 128) u28_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx29 & R29 & M29 & MS29 & K29 & R29_2 & R29_8 & R29_10 & R29_11 & FR29 & GR29).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu28_10. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF28 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF28); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF28 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF28); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_28 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_28); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_28 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_28); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS29.
  (* [comment removed for export] *)
  assert (AG29: forall a k, ((a + k <= (S - 480) \/ (S - 416) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M28 M29 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR29; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R29_2n: getr R29 (reg 2) = Z_to_bv 64 (S - 416)) by (rewrite R29_2; f_equal; ring). clear R29_2. rename R29_2n into R29_2.
  assert (R29_3: getr R29 (reg 3) = Z_to_bv 64 67584) by (kin K29 3%nat; exact R28_3).
  assert (R29_4: getr R29 (reg 4) = Z_to_bv 64 462648) by (kin K29 4%nat; exact R28_4).
  assert (R29_8n: getr R29 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R29_8; f_equal; ring). clear R29_8. rename R29_8n into R29_8.
  assert (R29_9: getr R29 (reg 9) = Z_to_bv 64 (S - 64)) by (kin K29 9%nat; exact R28_9).
  assert (R29_10n: getr R29 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R29_10; f_equal; ring). clear R29_10. rename R29_10n into R29_10.
  assert (R29_18: getr R29 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K29 18%nat; exact R28_18).
  assert (R29_19: getr R29 (reg 19) = Z_to_bv 64 w568) by (kin K29 19%nat; exact R28_19).
  assert (R29_20: getr R29 (reg 20) = Z_to_bv 64 w576) by (kin K29 20%nat; exact R28_20).
  assert (R29_21: getr R29 (reg 21) = Z_to_bv 64 w584) by (kin K29 21%nat; exact R28_21).
  assert (R29_22: getr R29 (reg 22) = Z_to_bv 64 w592) by (kin K29 22%nat; exact R28_22).
  assert (R29_23: getr R29 (reg 23) = Z_to_bv 64 w600) by (kin K29 23%nat; exact R28_23).
  assert (R29_24: getr R29 (reg 24) = Z_to_bv 64 w608) by (kin K29 24%nat; exact R28_24).
  assert (R29_25: getr R29 (reg 25) = Z_to_bv 64 w616) by (kin K29 25%nat; exact R28_25).
  assert (R29_26: getr R29 (reg 26) = Z_to_bv 64 w624) by (kin K29 26%nat; exact R28_26).
  assert (R29_27: getr R29 (reg 27) = Z_to_bv 64 w632) by (kin K29 27%nat; exact R28_27).
  assert (c29_Sm72: L5.u64_at RSEGS M29 (S - 72) 140436) by (clear - AG29 c28_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm72]).
  assert (c29_Sm80: L5.u64_at RSEGS M29 (S - 80) (S + 64)) by (clear - AG29 c28_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm80]).
  assert (c29_Sm88: L5.u64_at RSEGS M29 (S - 88) (U R0 9)) by (clear - AG29 c28_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm88]).
  assert (c29_Sm96: L5.u64_at RSEGS M29 (S - 96) (U R0 18)) by (clear - AG29 c28_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm96]).
  assert (c29_Sm104: L5.u64_at RSEGS M29 (S - 104) (U R0 19)) by (clear - AG29 c28_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm104]).
  assert (c29_Sm112: L5.u64_at RSEGS M29 (S - 112) (U R0 20)) by (clear - AG29 c28_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm112]).
  assert (c29_Sm120: L5.u64_at RSEGS M29 (S - 120) (U R0 21)) by (clear - AG29 c28_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm120]).
  assert (c29_Sm128: L5.u64_at RSEGS M29 (S - 128) (U R0 22)) by (clear - AG29 c28_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm128]).
  assert (c29_Sm136: L5.u64_at RSEGS M29 (S - 136) (U R0 23)) by (clear - AG29 c28_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm136]).
  assert (c29_Sm144: L5.u64_at RSEGS M29 (S - 144) (U R0 24)) by (clear - AG29 c28_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm144]).
  assert (c29_Sm152: L5.u64_at RSEGS M29 (S - 152) (U R0 25)) by (clear - AG29 c28_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm152]).
  assert (c29_Sm160: L5.u64_at RSEGS M29 (S - 160) (U R0 26)) by (clear - AG29 c28_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm160]).
  assert (c29_Sm168: L5.u64_at RSEGS M29 (S - 168) (U R0 27)) by (clear - AG29 c28_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm168]).
  assert (c29_Sm24: L5.u64_at RSEGS M29 (S - 24) 134416) by (clear - AG29 c28_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm24]).
  assert (c29_Sm32: L5.u64_at RSEGS M29 (S - 32) (S + 96)) by (clear - AG29 c28_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm32]).
  assert (c29_Sm8: L5.u64_at RSEGS M29 (S - 8) 133204) by (clear - AG29 c28_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm8]).
  assert (c29_Sm16: L5.u64_at RSEGS M29 (S - 16) (U R0 8)) by (clear - AG29 c28_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm16]).
  assert (c29_Sm344w1: L5.u8_at RSEGS M29 (S - 344) fb344) by (clear - AG29 c28_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Sm344w1]).
  assert (c29_Sm280w1: L5.u8_at RSEGS M29 (S - 280) fb280) by (clear - AG29 c28_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Sm280w1]).
  assert (c29_Sm248w1: L5.u8_at RSEGS M29 (S - 248) fb248) by (clear - AG29 c28_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Sm248w1]).
  assert (c29_Sm224: L5.u64_at RSEGS M29 (S - 224) d3) by (clear - AG29 c28_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm224]).
  assert (c29_Sm232: L5.u64_at RSEGS M29 (S - 232) 8) by (clear - AG29 c28_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm232]).
  assert (c29_Sm200w1: L5.u8_at RSEGS M29 (S - 200) fb200) by (clear - AG29 c28_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Sm200w1]).
  assert (c29_Sm176: L5.u64_at RSEGS M29 (S - 176) d4) by (clear - AG29 c28_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm176]).
  assert (c29_Sm184: L5.u64_at RSEGS M29 (S - 184) 8) by (clear - AG29 c28_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Sm184]).
  assert (c29_Sm64w1: L5.u8_at RSEGS M29 (S - 64) fb64) by (clear - AG29 c28_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Sm64w1]).
  assert (c29_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M29 (A + i) 0)) by (clear - AG29 c28_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | apply c28_Om128z8; exact Hi]).
  assert (c29_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M29 ((A + 48) + i) 0)) by (clear - AG29 c28_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | apply c28_Om80z12; exact Hi]).
  assert (c29_Op0: L5.u64_at RSEGS M29 (A + 128) 376080) by (clear - AG29 c28_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Op0]).
  assert (c29_Op8: L5.u64_at RSEGS M29 (A + 136) (ref + 24)) by (clear - AG29 c28_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Op8]).
  assert (c29_Fp24: L5.u64_at RSEGS M29 (ref + 24) 8028075845441778529) by (clear - AG29 c28_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp24]).
  assert (c29_Fp32: L5.u64_at RSEGS M29 (ref + 32) 7863351059373564014) by (clear - AG29 c28_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp32]).
  assert (c29_Fp40: L5.u64_at RSEGS M29 (ref + 40) 2838809733452757089) by (clear - AG29 c28_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp40]).
  assert (c29_Fp48: L5.u64_at RSEGS M29 (ref + 48) 2334102023183623712) by (clear - AG29 c28_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp48]).
  assert (c29_Fp56: L5.u64_at RSEGS M29 (ref + 56) 4188416081412519009) by (clear - AG29 c28_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp56]).
  assert (c29_Fp64w1: L5.u8_at RSEGS M29 (ref + 64) 48) by (clear - AG29 c28_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Fp64w1]).
  assert (c29_Fp65w1: L5.u8_at RSEGS M29 (ref + 65) 0) by (clear - AG29 c28_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M28 M29 _ _ _ (AG29 _ 1)); [lia | exact c28_Fp65w1]).
  assert (c29_Fp16w4: L5.u32_at RSEGS M29 (ref + 16) 0) by (clear - AG29 c28_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M28 M29 _ _ _ (AG29 _ 4)); [lia | exact c28_Fp16w4]).
  assert (c29_Fp8: L5.u64_at RSEGS M29 (ref + 8) 41) by (clear - AG29 c28_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp8]).
  assert (c29_Fp0: L5.u64_at RSEGS M29 ref 41) by (clear - AG29 c28_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Fp0]).
  assert (c29_Om8: L5.u64_at RSEGS M29 (A + 120) S) by (clear - AG29 c28_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om8]).
  assert (c29_Om40: L5.u64_at RSEGS M29 (A + 88) (A + 128)) by (clear - AG29 c28_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om40]).
  assert (c29_Om48: L5.u64_at RSEGS M29 (A + 80) 133556) by (clear - AG29 c28_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om48]).
  assert (c29_Om56: L5.u64_at RSEGS M29 (A + 72) 91856) by (clear - AG29 c28_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om56]).
  assert (c29_Om64: L5.u64_at RSEGS M29 (A + 64) 91995) by (clear - AG29 c28_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om64]).
  assert (c29_Om68w4: L5.u32_at RSEGS M29 (A + 60) 1) by (clear - AG29 c28_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M28 M29 _ _ _ (AG29 _ 4)); [lia | exact c28_Om68w4]).
  assert (c29_Om16: L5.u64_at RSEGS M29 (A + 112) 0) by (clear - AG29 c28_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om16]).
  assert (c29_Om120: L5.u64_at RSEGS M29 (A + 8) 1) by (clear - AG29 c28_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om120]).
  assert (c29_Om24: L5.u64_at RSEGS M29 (A + 104) 260436) by (clear - AG29 c28_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om24]).
  assert (c29_Om32: L5.u64_at RSEGS M29 (A + 96) 4849336966747728640) by (clear - AG29 c28_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om32]).
  assert (c29_Om88: L5.u64_at RSEGS M29 (A + 40) 145512) by (clear - AG29 c28_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om88]).
  assert (c29_Om104: L5.u64_at RSEGS M29 (A + 24) 256628) by (clear - AG29 c28_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om104]).
  assert (c29_Om112: L5.u64_at RSEGS M29 (A + 16) 376040) by (clear - AG29 c28_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om112]).
  assert (c29_Om96: L5.u64_at RSEGS M29 (A + 32) 145780) by (clear - AG29 c28_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M28 M29 _ _ _ (AG29 _ 8)); [lia | exact c28_Om96]).
  assert (STAT29: forall a, stat_rd av a -> M29 (Z_to_bv 64 a) = M28 (Z_to_bv 64 a)).
  { clear - FR29 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR29; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M28 M29 gd av uid rnd canary hw ES28 STAT29) as ES29.
  assert (DEF29: L5.defined M29 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR29 | exact DEF28]).
  assert (DEFref_29: L5.defined M29 ref 66) by (eapply L5.defined_grows; [exact GR29 | exact DEFref_28]).
  assert (DEFA_29: L5.defined M29 A 144) by (eapply L5.defined_grows; [exact GR29 | exact DEFA_28]).
  assert (HH29: hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M29 (m_vmmaps model28)).
  { clear - HH28 GR29 FR29 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH28. lia. 2: exact GR29. intros a Ha.
    destruct (in_dec (S - 480) (S - 416) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR29; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ29: L5C.hpres L LB1 S 10240 XSF M M29).
  { clear - LBWF HQ28 FR29 GR29 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M28 M29 [((S - 480), 64)]). exact LBWF. lia. exact HQ28.
    { intros x Hx. apply FR29; intros Hin.
        apply (Hx ((S - 480), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR29.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG29 FR29 MS29. try clear STAT29. try clear K28.
  try clear c28_Sm72. try clear c28_Sm80. try clear c28_Sm88. try clear c28_Sm96. try clear c28_Sm104. try clear c28_Sm112. try clear c28_Sm120. try clear c28_Sm128. try clear c28_Sm136. try clear c28_Sm144. try clear c28_Sm152. try clear c28_Sm160. try clear c28_Sm168. try clear c28_Sm24. try clear c28_Sm32. try clear c28_Sm8. try clear c28_Sm16. try clear c28_Sm344w1. try clear c28_Sm280w1. try clear c28_Sm248w1. try clear c28_Sm224. try clear c28_Sm232. try clear c28_Sm200w1. try clear c28_Sm176. try clear c28_Sm184. try clear c28_Sm64w1. try clear c28_Om128z8. try clear c28_Om80z12. try clear c28_Op0. try clear c28_Op8. try clear c28_Fp24. try clear c28_Fp32. try clear c28_Fp40. try clear c28_Fp48. try clear c28_Fp56. try clear c28_Fp64w1. try clear c28_Fp65w1. try clear c28_Fp16w4. try clear c28_Fp8. try clear c28_Fp0. try clear c28_Om8. try clear c28_Om40. try clear c28_Om48. try clear c28_Om56. try clear c28_Om64. try clear c28_Om68w4. try clear c28_Om16. try clear c28_Om120. try clear c28_Om24. try clear c28_Om32. try clear c28_Om88. try clear c28_Om104. try clear c28_Om112. try clear c28_Om96. try clear R28_2. try clear R28_3. try clear R28_4. try clear R28_8. try clear R28_9. try clear R28_18. try clear R28_19. try clear R28_20. try clear R28_21. try clear R28_22. try clear R28_23. try clear R28_24. try clear R28_25. try clear R28_26. try clear R28_27. try clear R28_10. try clear DEF28. try clear HH28. try clear HQ28. try clear ES28. try clear DEFref_28. try clear DEFA_28.
  (* [comment removed for export] *)
  pose proof ES29 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M29 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r5u_conc fx29 R29 M29 (S - 1008) (A + 128) av canary uid rnd hw (U R0 9) (U R0 18) (U R0 19) (U R0 20) (U R0 21) (U R0 22) (U R0 23) (U R0 24) (U R0 25) (U R0 26) (U R0 27) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx30 & R30 & M30 & MS30 & K30 & R30_1 & R30_2 & R30_8 & R30_9 & R30_10 & R30_11 & R30_18 & R30_19 & R30_20 & R30_21 & R30_22 & R30_23 & R30_24 & R30_25 & R30_26 & R30_27 & FR30 & GR30).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI S_21. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI S_19. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI S_20. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI S_22. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF29 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF29); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF29 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF29); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_29 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_29); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_29 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_29); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c29_Om16 | cellfix c29_Om16]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c29_Om8 | cellfix c29_Om8]. }
  { (* [comment removed for export] *) first [exact c29_Om32 | cellfix c29_Om32]. }
  { (* [comment removed for export] *) first [exact c29_Sm72 | cellfix c29_Sm72]. }
  { (* [comment removed for export] *) first [exact c29_Sm80 | cellfix c29_Sm80]. }
  { (* [comment removed for export] *) first [exact c29_Sm88 | cellfix c29_Sm88]. }
  { (* [comment removed for export] *) first [exact c29_Sm96 | cellfix c29_Sm96]. }
  { (* [comment removed for export] *) first [exact c29_Sm104 | cellfix c29_Sm104]. }
  { (* [comment removed for export] *) first [exact c29_Sm112 | cellfix c29_Sm112]. }
  { (* [comment removed for export] *) first [exact c29_Sm120 | cellfix c29_Sm120]. }
  { (* [comment removed for export] *) first [exact c29_Sm128 | cellfix c29_Sm128]. }
  { (* [comment removed for export] *) first [exact c29_Sm136 | cellfix c29_Sm136]. }
  { (* [comment removed for export] *) first [exact c29_Sm144 | cellfix c29_Sm144]. }
  { (* [comment removed for export] *) first [exact c29_Sm152 | cellfix c29_Sm152]. }
  { (* [comment removed for export] *) first [exact c29_Sm160 | cellfix c29_Sm160]. }
  { (* [comment removed for export] *) first [exact c29_Sm168 | cellfix c29_Sm168]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS30.
  (* [comment removed for export] *)
  assert (AG30: forall a k, ((a + k <= (S - 8944) \/ (S - 416) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M29 M30 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR30; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R30_1n: getr R30 (reg 1) = Z_to_bv 64 140488) by (rewrite R30_1; f_equal; ring). clear R30_1. rename R30_1n into R30_1.
  assert (R30_2n: getr R30 (reg 2) = Z_to_bv 64 (S - 64)) by (rewrite R30_2; f_equal; ring). clear R30_2. rename R30_2n into R30_2.
  assert (R30_3: getr R30 (reg 3) = Z_to_bv 64 67584) by (kin K30 3%nat; exact R29_3).
  assert (R30_4: getr R30 (reg 4) = Z_to_bv 64 462648) by (kin K30 4%nat; exact R29_4).
  assert (R30_8n: getr R30 (reg 8) = Z_to_bv 64 (S + 64)) by (rewrite R30_8; f_equal; ring). clear R30_8. rename R30_8n into R30_8.
  assert (R30_9n: getr R30 (reg 9) = Z_to_bv 64 (U R0 9)) by (rewrite R30_9; f_equal; ring). clear R30_9. rename R30_9n into R30_9.
  assert (R30_10n: getr R30 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R30_10; f_equal; ring). clear R30_10. rename R30_10n into R30_10.
  assert (R30_11n: getr R30 (reg 11) = Z_to_bv 64 0) by (rewrite R30_11; f_equal; ring). clear R30_11. rename R30_11n into R30_11.
  assert (R30_18n: getr R30 (reg 18) = Z_to_bv 64 (U R0 18)) by (rewrite R30_18; f_equal; ring). clear R30_18. rename R30_18n into R30_18.
  assert (R30_19n: getr R30 (reg 19) = Z_to_bv 64 (U R0 19)) by (rewrite R30_19; f_equal; ring). clear R30_19. rename R30_19n into R30_19.
  assert (R30_20n: getr R30 (reg 20) = Z_to_bv 64 (U R0 20)) by (rewrite R30_20; f_equal; ring). clear R30_20. rename R30_20n into R30_20.
  assert (R30_21n: getr R30 (reg 21) = Z_to_bv 64 (U R0 21)) by (rewrite R30_21; f_equal; ring). clear R30_21. rename R30_21n into R30_21.
  assert (R30_22n: getr R30 (reg 22) = Z_to_bv 64 (U R0 22)) by (rewrite R30_22; f_equal; ring). clear R30_22. rename R30_22n into R30_22.
  assert (R30_23n: getr R30 (reg 23) = Z_to_bv 64 (U R0 23)) by (rewrite R30_23; f_equal; ring). clear R30_23. rename R30_23n into R30_23.
  assert (R30_24n: getr R30 (reg 24) = Z_to_bv 64 (U R0 24)) by (rewrite R30_24; f_equal; ring). clear R30_24. rename R30_24n into R30_24.
  assert (R30_25n: getr R30 (reg 25) = Z_to_bv 64 (U R0 25)) by (rewrite R30_25; f_equal; ring). clear R30_25. rename R30_25n into R30_25.
  assert (R30_26n: getr R30 (reg 26) = Z_to_bv 64 (U R0 26)) by (rewrite R30_26; f_equal; ring). clear R30_26. rename R30_26n into R30_26.
  assert (R30_27n: getr R30 (reg 27) = Z_to_bv 64 (U R0 27)) by (rewrite R30_27; f_equal; ring). clear R30_27. rename R30_27n into R30_27.
  assert (c30_Sm72: L5.u64_at RSEGS M30 (S - 72) 140436) by (clear - AG30 c29_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm72]).
  assert (c30_Sm80: L5.u64_at RSEGS M30 (S - 80) (S + 64)) by (clear - AG30 c29_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm80]).
  assert (c30_Sm88: L5.u64_at RSEGS M30 (S - 88) (U R0 9)) by (clear - AG30 c29_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm88]).
  assert (c30_Sm96: L5.u64_at RSEGS M30 (S - 96) (U R0 18)) by (clear - AG30 c29_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm96]).
  assert (c30_Sm104: L5.u64_at RSEGS M30 (S - 104) (U R0 19)) by (clear - AG30 c29_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm104]).
  assert (c30_Sm112: L5.u64_at RSEGS M30 (S - 112) (U R0 20)) by (clear - AG30 c29_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm112]).
  assert (c30_Sm120: L5.u64_at RSEGS M30 (S - 120) (U R0 21)) by (clear - AG30 c29_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm120]).
  assert (c30_Sm128: L5.u64_at RSEGS M30 (S - 128) (U R0 22)) by (clear - AG30 c29_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm128]).
  assert (c30_Sm136: L5.u64_at RSEGS M30 (S - 136) (U R0 23)) by (clear - AG30 c29_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm136]).
  assert (c30_Sm144: L5.u64_at RSEGS M30 (S - 144) (U R0 24)) by (clear - AG30 c29_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm144]).
  assert (c30_Sm152: L5.u64_at RSEGS M30 (S - 152) (U R0 25)) by (clear - AG30 c29_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm152]).
  assert (c30_Sm160: L5.u64_at RSEGS M30 (S - 160) (U R0 26)) by (clear - AG30 c29_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm160]).
  assert (c30_Sm168: L5.u64_at RSEGS M30 (S - 168) (U R0 27)) by (clear - AG30 c29_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm168]).
  assert (c30_Sm24: L5.u64_at RSEGS M30 (S - 24) 134416) by (clear - AG30 c29_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm24]).
  assert (c30_Sm32: L5.u64_at RSEGS M30 (S - 32) (S + 96)) by (clear - AG30 c29_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm32]).
  assert (c30_Sm8: L5.u64_at RSEGS M30 (S - 8) 133204) by (clear - AG30 c29_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm8]).
  assert (c30_Sm16: L5.u64_at RSEGS M30 (S - 16) (U R0 8)) by (clear - AG30 c29_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm16]).
  assert (c30_Sm344w1: L5.u8_at RSEGS M30 (S - 344) fb344) by (clear - AG30 c29_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Sm344w1]).
  assert (c30_Sm280w1: L5.u8_at RSEGS M30 (S - 280) fb280) by (clear - AG30 c29_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Sm280w1]).
  assert (c30_Sm248w1: L5.u8_at RSEGS M30 (S - 248) fb248) by (clear - AG30 c29_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Sm248w1]).
  assert (c30_Sm224: L5.u64_at RSEGS M30 (S - 224) d3) by (clear - AG30 c29_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm224]).
  assert (c30_Sm232: L5.u64_at RSEGS M30 (S - 232) 8) by (clear - AG30 c29_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm232]).
  assert (c30_Sm200w1: L5.u8_at RSEGS M30 (S - 200) fb200) by (clear - AG30 c29_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Sm200w1]).
  assert (c30_Sm176: L5.u64_at RSEGS M30 (S - 176) d4) by (clear - AG30 c29_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm176]).
  assert (c30_Sm184: L5.u64_at RSEGS M30 (S - 184) 8) by (clear - AG30 c29_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Sm184]).
  assert (c30_Sm64w1: L5.u8_at RSEGS M30 (S - 64) fb64) by (clear - AG30 c29_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Sm64w1]).
  assert (c30_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M30 (A + i) 0)) by (clear - AG30 c29_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | apply c29_Om128z8; exact Hi]).
  assert (c30_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M30 ((A + 48) + i) 0)) by (clear - AG30 c29_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | apply c29_Om80z12; exact Hi]).
  assert (c30_Op0: L5.u64_at RSEGS M30 (A + 128) 376080) by (clear - AG30 c29_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Op0]).
  assert (c30_Op8: L5.u64_at RSEGS M30 (A + 136) (ref + 24)) by (clear - AG30 c29_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Op8]).
  assert (c30_Fp24: L5.u64_at RSEGS M30 (ref + 24) 8028075845441778529) by (clear - AG30 c29_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp24]).
  assert (c30_Fp32: L5.u64_at RSEGS M30 (ref + 32) 7863351059373564014) by (clear - AG30 c29_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp32]).
  assert (c30_Fp40: L5.u64_at RSEGS M30 (ref + 40) 2838809733452757089) by (clear - AG30 c29_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp40]).
  assert (c30_Fp48: L5.u64_at RSEGS M30 (ref + 48) 2334102023183623712) by (clear - AG30 c29_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp48]).
  assert (c30_Fp56: L5.u64_at RSEGS M30 (ref + 56) 4188416081412519009) by (clear - AG30 c29_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp56]).
  assert (c30_Fp64w1: L5.u8_at RSEGS M30 (ref + 64) 48) by (clear - AG30 c29_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Fp64w1]).
  assert (c30_Fp65w1: L5.u8_at RSEGS M30 (ref + 65) 0) by (clear - AG30 c29_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M29 M30 _ _ _ (AG30 _ 1)); [lia | exact c29_Fp65w1]).
  assert (c30_Fp16w4: L5.u32_at RSEGS M30 (ref + 16) 0) by (clear - AG30 c29_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M29 M30 _ _ _ (AG30 _ 4)); [lia | exact c29_Fp16w4]).
  assert (c30_Fp8: L5.u64_at RSEGS M30 (ref + 8) 41) by (clear - AG30 c29_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp8]).
  assert (c30_Fp0: L5.u64_at RSEGS M30 ref 41) by (clear - AG30 c29_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Fp0]).
  assert (c30_Om8: L5.u64_at RSEGS M30 (A + 120) S) by (clear - AG30 c29_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om8]).
  assert (c30_Om40: L5.u64_at RSEGS M30 (A + 88) (A + 128)) by (clear - AG30 c29_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om40]).
  assert (c30_Om48: L5.u64_at RSEGS M30 (A + 80) 133556) by (clear - AG30 c29_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om48]).
  assert (c30_Om56: L5.u64_at RSEGS M30 (A + 72) 91856) by (clear - AG30 c29_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om56]).
  assert (c30_Om64: L5.u64_at RSEGS M30 (A + 64) 91995) by (clear - AG30 c29_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om64]).
  assert (c30_Om68w4: L5.u32_at RSEGS M30 (A + 60) 1) by (clear - AG30 c29_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M29 M30 _ _ _ (AG30 _ 4)); [lia | exact c29_Om68w4]).
  assert (c30_Om16: L5.u64_at RSEGS M30 (A + 112) 0) by (clear - AG30 c29_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om16]).
  assert (c30_Om120: L5.u64_at RSEGS M30 (A + 8) 1) by (clear - AG30 c29_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om120]).
  assert (c30_Om24: L5.u64_at RSEGS M30 (A + 104) 260436) by (clear - AG30 c29_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om24]).
  assert (c30_Om32: L5.u64_at RSEGS M30 (A + 96) 4849336966747728640) by (clear - AG30 c29_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om32]).
  assert (c30_Om88: L5.u64_at RSEGS M30 (A + 40) 145512) by (clear - AG30 c29_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om88]).
  assert (c30_Om104: L5.u64_at RSEGS M30 (A + 24) 256628) by (clear - AG30 c29_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om104]).
  assert (c30_Om112: L5.u64_at RSEGS M30 (A + 16) 376040) by (clear - AG30 c29_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om112]).
  assert (c30_Om96: L5.u64_at RSEGS M30 (A + 32) 145780) by (clear - AG30 c29_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M29 M30 _ _ _ (AG30 _ 8)); [lia | exact c29_Om96]).
  assert (STAT30: forall a, stat_rd av a -> M30 (Z_to_bv 64 a) = M29 (Z_to_bv 64 a)).
  { clear - FR30 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR30; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M29 M30 gd av uid rnd canary hw ES29 STAT30) as ES30.
  assert (DEF30: L5.defined M30 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR30 | exact DEF29]).
  assert (DEFref_30: L5.defined M30 ref 66) by (eapply L5.defined_grows; [exact GR30 | exact DEFref_29]).
  assert (DEFA_30: L5.defined M30 A 144) by (eapply L5.defined_grows; [exact GR30 | exact DEFA_29]).
  assert (HH30: hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M30 (m_vmmaps model28)).
  { clear - HH29 GR30 FR30 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH29. lia. 2: exact GR30. intros a Ha.
    destruct (in_dec (S - 8944) (S - 416) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR30; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ30: L5C.hpres L LB1 S 10240 XSF M M30).
  { clear - LBWF HQ29 FR30 GR30 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M29 M30 [((S - 8944), 8528)]). exact LBWF. lia. exact HQ29.
    { intros x Hx. apply FR30; intros Hin.
        apply (Hx ((S - 8944), 8528)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR30.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG30 FR30 MS30. try clear STAT30. try clear K29.
  try clear c29_Sm72. try clear c29_Sm80. try clear c29_Sm88. try clear c29_Sm96. try clear c29_Sm104. try clear c29_Sm112. try clear c29_Sm120. try clear c29_Sm128. try clear c29_Sm136. try clear c29_Sm144. try clear c29_Sm152. try clear c29_Sm160. try clear c29_Sm168. try clear c29_Sm24. try clear c29_Sm32. try clear c29_Sm8. try clear c29_Sm16. try clear c29_Sm344w1. try clear c29_Sm280w1. try clear c29_Sm248w1. try clear c29_Sm224. try clear c29_Sm232. try clear c29_Sm200w1. try clear c29_Sm176. try clear c29_Sm184. try clear c29_Sm64w1. try clear c29_Om128z8. try clear c29_Om80z12. try clear c29_Op0. try clear c29_Op8. try clear c29_Fp24. try clear c29_Fp32. try clear c29_Fp40. try clear c29_Fp48. try clear c29_Fp56. try clear c29_Fp64w1. try clear c29_Fp65w1. try clear c29_Fp16w4. try clear c29_Fp8. try clear c29_Fp0. try clear c29_Om8. try clear c29_Om40. try clear c29_Om48. try clear c29_Om56. try clear c29_Om64. try clear c29_Om68w4. try clear c29_Om16. try clear c29_Om120. try clear c29_Om24. try clear c29_Om32. try clear c29_Om88. try clear c29_Om104. try clear c29_Om112. try clear c29_Om96. try clear R29_2. try clear R29_3. try clear R29_4. try clear R29_8. try clear R29_9. try clear R29_10. try clear R29_18. try clear R29_19. try clear R29_20. try clear R29_21. try clear R29_22. try clear R29_23. try clear R29_24. try clear R29_25. try clear R29_26. try clear R29_27. try clear DEF29. try clear HH29. try clear HQ29. try clear ES29. try clear DEFref_29. try clear DEFA_29.
  eapply (seg17 fx30 R0 R R30 M M30 model model28 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 R30_1 R30_2 R30_3 R30_4 R30_8 R30_9 R30_10 R30_11 R30_18 R30_19 R30_20 R30_21 R30_22 R30_23 R30_24 R30_25 R30_26 R30_27 c30_Sm72 c30_Sm80 c30_Sm88 c30_Sm96 c30_Sm104 c30_Sm112 c30_Sm120 c30_Sm128 c30_Sm136 c30_Sm144 c30_Sm152 c30_Sm160 c30_Sm168 c30_Sm24 c30_Sm32 c30_Sm8 c30_Sm16 c30_Sm344w1 c30_Sm280w1 c30_Sm248w1 c30_Sm224 c30_Sm232 c30_Sm200w1 c30_Sm176 c30_Sm184 c30_Sm64w1 c30_Om128z8 c30_Om80z12 c30_Op0 c30_Op8 c30_Fp24 c30_Fp32 c30_Fp40 c30_Fp48 c30_Fp56 c30_Fp64w1 c30_Fp65w1 c30_Fp16w4 c30_Fp8 c30_Fp0 c30_Om8 c30_Om40 c30_Om48 c30_Om56 c30_Om64 c30_Om68w4 c30_Om16 c30_Om120 c30_Om24 c30_Om32 c30_Om88 c30_Om104 c30_Om112 c30_Om96 ES30 DEF30 DEFref_30 DEFA_30 BR_ref BR_A AP_ref_A FRSH_ref FRSH_A HH30 MOK28 MBV28 HQ30 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3US16.
