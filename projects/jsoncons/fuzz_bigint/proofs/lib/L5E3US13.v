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
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3AU L5E3T0U L5E3T1U L5E3PU L5E3R1U L5E3R2U L5E3US14.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3US13.
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
Let seg14 := L5E3US14.seg14 L HI LY LYX HIok.

Lemma seg13 (fx22 : FPState) (R0 R R22 : bvmap 5 word) (M M22 : word -> option byte) (model model18 : Model) (K : TSet)
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
  (* [comment removed for export] *) getr R22 (reg 1) = Z_to_bv 64 143836 ->
  (* [comment removed for export] *) getr R22 (reg 2) = Z_to_bv 64 (S - 480) ->
  (* [comment removed for export] *) getr R22 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R22 (reg 4) = Z_to_bv 64 462648 ->
  (* [comment removed for export] *) getr R22 (reg 8) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R22 (reg 9) = Z_to_bv 64 w552 ->
  (* [comment removed for export] *) getr R22 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R22 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R22 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R22 (reg 19) = Z_to_bv 64 w568 ->
  (* [comment removed for export] *) getr R22 (reg 20) = Z_to_bv 64 w576 ->
  (* [comment removed for export] *) getr R22 (reg 21) = Z_to_bv 64 w584 ->
  (* [comment removed for export] *) getr R22 (reg 22) = Z_to_bv 64 w592 ->
  (* [comment removed for export] *) getr R22 (reg 23) = Z_to_bv 64 w600 ->
  (* [comment removed for export] *) getr R22 (reg 24) = Z_to_bv 64 w608 ->
  (* [comment removed for export] *) getr R22 (reg 25) = Z_to_bv 64 w616 ->
  (* [comment removed for export] *) getr R22 (reg 26) = Z_to_bv 64 w624 ->
  (* [comment removed for export] *) getr R22 (reg 27) = Z_to_bv 64 w632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 488) 143756 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 424) 141856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 440) (S - 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 72) 140436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 80) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 88) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 96) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 104) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 112) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 120) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 128) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 136) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 144) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 152) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 160) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 168) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 24) 134416 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 32) (S + 96) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 8) 133204 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 528) fb528 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 472) fb472 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 344) fb344 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 224) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 232) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 200) fb200 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 176) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (S - 184) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (S - 64) fb64 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M22 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M22 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 128) 376080 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M22 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M22 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 80) 133556 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 72) 91856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 64) 91995 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M22 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 104) 260436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 40) 145512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 24) 256628 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 16) 376040 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M22 (A + 32) 145780 ->
  (* [comment removed for export] *) L5USU.statics_landed M22 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M22 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M22 ref 66 ->
  (* [comment removed for export] *) L5.defined M22 A 144 ->
  (* [comment removed for export] *) L5.defined M22 d3 64 ->
  (* [comment removed for export] *) L5.defined M22 d4 64 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d3 \/ d3 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d4 \/ d4 + 64 <= ref) ->
  (* [comment removed for export] *) (A + 144 <= d3 \/ d3 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d4 \/ d4 + 64 <= A) ->
  (* [comment removed for export] *) (d3 + 64 <= d4 \/ d4 + 64 <= d3) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M22 (m_vmmaps model18) ->
  (* [comment removed for export] *) model_ok model18 ->
  (* [comment removed for export] *) model_but_vm model model18 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M22 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5USU.e3_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133556 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx22 R22 143836 M22 model18) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 R22_1 R22_2 R22_3 R22_4 R22_8 R22_9 R22_10 R22_11 R22_18 R22_19 R22_20 R22_21 R22_22 R22_23 R22_24 R22_25 R22_26 R22_27 c22_Sm488 c22_Sm496 c22_Sm424 c22_Sm432 c22_Sm440 c22_Sm72 c22_Sm80 c22_Sm88 c22_Sm96 c22_Sm104 c22_Sm112 c22_Sm120 c22_Sm128 c22_Sm136 c22_Sm144 c22_Sm152 c22_Sm160 c22_Sm168 c22_Sm24 c22_Sm32 c22_Sm8 c22_Sm16 c22_Sm528w1 c22_Sm472w1 c22_Sm344w1 c22_Sm280w1 c22_Sm248w1 c22_Sm224 c22_Sm232 c22_Sm200w1 c22_Sm176 c22_Sm184 c22_Sm64w1 c22_Om128z8 c22_Om80z12 c22_Op0 c22_Op8 c22_Fp24 c22_Fp32 c22_Fp40 c22_Fp48 c22_Fp56 c22_Fp64w1 c22_Fp65w1 c22_Fp16w4 c22_Fp8 c22_Fp0 c22_Om8 c22_Om40 c22_Om48 c22_Om56 c22_Om64 c22_Om68w4 c22_Om16 c22_Om120 c22_Om24 c22_Om32 c22_Om88 c22_Om104 c22_Om112 c22_Om96 ES22 DEF22 DEFref_22 DEFA_22 DEFd3_22 DEFd4_22 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH22 MOK18 MBV18 HQ22 KE.
  pose proof MOK18 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES22 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 1008) mod 16 = 0). { clear - A16. replace (S - 1008) with (S + (-63) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES22 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M22 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p4u_conc fx22 R22 M22 (S - 1008) (A + 128) fb472 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx23 & R23 & M23 & MS23 & K23 & R23_2 & R23_8 & R23_10 & R23_11 & FR23 & GR23).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb472. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF22 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF22); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF22 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF22); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_22 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_22); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_22 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_22); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb472. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c22_Sm472w1 | cellfix c22_Sm472w1]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS23.
  (* [comment removed for export] *)
  assert (AG23: forall a k, ((a + k <= (S - 544) \/ (S - 480) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M22 M23 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR23; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R23_1: getr R23 (reg 1) = Z_to_bv 64 143836) by (kin K23 1%nat; exact R22_1).
  assert (R23_2n: getr R23 (reg 2) = Z_to_bv 64 (S - 480)) by (rewrite R23_2; f_equal; ring). clear R23_2. rename R23_2n into R23_2.
  assert (R23_3: getr R23 (reg 3) = Z_to_bv 64 67584) by (kin K23 3%nat; exact R22_3).
  assert (R23_4: getr R23 (reg 4) = Z_to_bv 64 462648) by (kin K23 4%nat; exact R22_4).
  assert (R23_8n: getr R23 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R23_8; f_equal; ring). clear R23_8. rename R23_8n into R23_8.
  assert (R23_9: getr R23 (reg 9) = Z_to_bv 64 w552) by (kin K23 9%nat; exact R22_9).
  assert (R23_10n: getr R23 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R23_10; f_equal; ring). clear R23_10. rename R23_10n into R23_10.
  assert (R23_11n: getr R23 (reg 11) = Z_to_bv 64 0) by (rewrite R23_11; f_equal; ring). clear R23_11. rename R23_11n into R23_11.
  assert (R23_18: getr R23 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K23 18%nat; exact R22_18).
  assert (R23_19: getr R23 (reg 19) = Z_to_bv 64 w568) by (kin K23 19%nat; exact R22_19).
  assert (R23_20: getr R23 (reg 20) = Z_to_bv 64 w576) by (kin K23 20%nat; exact R22_20).
  assert (R23_21: getr R23 (reg 21) = Z_to_bv 64 w584) by (kin K23 21%nat; exact R22_21).
  assert (R23_22: getr R23 (reg 22) = Z_to_bv 64 w592) by (kin K23 22%nat; exact R22_22).
  assert (R23_23: getr R23 (reg 23) = Z_to_bv 64 w600) by (kin K23 23%nat; exact R22_23).
  assert (R23_24: getr R23 (reg 24) = Z_to_bv 64 w608) by (kin K23 24%nat; exact R22_24).
  assert (R23_25: getr R23 (reg 25) = Z_to_bv 64 w616) by (kin K23 25%nat; exact R22_25).
  assert (R23_26: getr R23 (reg 26) = Z_to_bv 64 w624) by (kin K23 26%nat; exact R22_26).
  assert (R23_27: getr R23 (reg 27) = Z_to_bv 64 w632) by (kin K23 27%nat; exact R22_27).
  assert (c23_Sm424: L5.u64_at RSEGS M23 (S - 424) 141856) by (clear - AG23 c22_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm424]).
  assert (c23_Sm432: L5.u64_at RSEGS M23 (S - 432) (S + 64)) by (clear - AG23 c22_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm432]).
  assert (c23_Sm440: L5.u64_at RSEGS M23 (S - 440) (S - 64)) by (clear - AG23 c22_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm440]).
  assert (c23_Sm72: L5.u64_at RSEGS M23 (S - 72) 140436) by (clear - AG23 c22_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm72]).
  assert (c23_Sm80: L5.u64_at RSEGS M23 (S - 80) (S + 64)) by (clear - AG23 c22_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm80]).
  assert (c23_Sm88: L5.u64_at RSEGS M23 (S - 88) (U R0 9)) by (clear - AG23 c22_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm88]).
  assert (c23_Sm96: L5.u64_at RSEGS M23 (S - 96) (U R0 18)) by (clear - AG23 c22_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm96]).
  assert (c23_Sm104: L5.u64_at RSEGS M23 (S - 104) (U R0 19)) by (clear - AG23 c22_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm104]).
  assert (c23_Sm112: L5.u64_at RSEGS M23 (S - 112) (U R0 20)) by (clear - AG23 c22_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm112]).
  assert (c23_Sm120: L5.u64_at RSEGS M23 (S - 120) (U R0 21)) by (clear - AG23 c22_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm120]).
  assert (c23_Sm128: L5.u64_at RSEGS M23 (S - 128) (U R0 22)) by (clear - AG23 c22_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm128]).
  assert (c23_Sm136: L5.u64_at RSEGS M23 (S - 136) (U R0 23)) by (clear - AG23 c22_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm136]).
  assert (c23_Sm144: L5.u64_at RSEGS M23 (S - 144) (U R0 24)) by (clear - AG23 c22_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm144]).
  assert (c23_Sm152: L5.u64_at RSEGS M23 (S - 152) (U R0 25)) by (clear - AG23 c22_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm152]).
  assert (c23_Sm160: L5.u64_at RSEGS M23 (S - 160) (U R0 26)) by (clear - AG23 c22_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm160]).
  assert (c23_Sm168: L5.u64_at RSEGS M23 (S - 168) (U R0 27)) by (clear - AG23 c22_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm168]).
  assert (c23_Sm24: L5.u64_at RSEGS M23 (S - 24) 134416) by (clear - AG23 c22_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm24]).
  assert (c23_Sm32: L5.u64_at RSEGS M23 (S - 32) (S + 96)) by (clear - AG23 c22_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm32]).
  assert (c23_Sm8: L5.u64_at RSEGS M23 (S - 8) 133204) by (clear - AG23 c22_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm8]).
  assert (c23_Sm16: L5.u64_at RSEGS M23 (S - 16) (U R0 8)) by (clear - AG23 c22_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm16]).
  assert (c23_Sm472w1: L5.u8_at RSEGS M23 (S - 472) fb472) by (clear - AG23 c22_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm472w1]).
  assert (c23_Sm344w1: L5.u8_at RSEGS M23 (S - 344) fb344) by (clear - AG23 c22_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm344w1]).
  assert (c23_Sm280w1: L5.u8_at RSEGS M23 (S - 280) fb280) by (clear - AG23 c22_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm280w1]).
  assert (c23_Sm248w1: L5.u8_at RSEGS M23 (S - 248) fb248) by (clear - AG23 c22_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm248w1]).
  assert (c23_Sm224: L5.u64_at RSEGS M23 (S - 224) d3) by (clear - AG23 c22_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm224]).
  assert (c23_Sm232: L5.u64_at RSEGS M23 (S - 232) 8) by (clear - AG23 c22_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm232]).
  assert (c23_Sm200w1: L5.u8_at RSEGS M23 (S - 200) fb200) by (clear - AG23 c22_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm200w1]).
  assert (c23_Sm176: L5.u64_at RSEGS M23 (S - 176) d4) by (clear - AG23 c22_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm176]).
  assert (c23_Sm184: L5.u64_at RSEGS M23 (S - 184) 8) by (clear - AG23 c22_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Sm184]).
  assert (c23_Sm64w1: L5.u8_at RSEGS M23 (S - 64) fb64) by (clear - AG23 c22_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Sm64w1]).
  assert (c23_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M23 (A + i) 0)) by (clear - AG23 c22_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | apply c22_Om128z8; exact Hi]).
  assert (c23_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M23 ((A + 48) + i) 0)) by (clear - AG23 c22_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | apply c22_Om80z12; exact Hi]).
  assert (c23_Op0: L5.u64_at RSEGS M23 (A + 128) 376080) by (clear - AG23 c22_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Op0]).
  assert (c23_Op8: L5.u64_at RSEGS M23 (A + 136) (ref + 24)) by (clear - AG23 c22_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Op8]).
  assert (c23_Fp24: L5.u64_at RSEGS M23 (ref + 24) 8028075845441778529) by (clear - AG23 c22_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp24]).
  assert (c23_Fp32: L5.u64_at RSEGS M23 (ref + 32) 7863351059373564014) by (clear - AG23 c22_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp32]).
  assert (c23_Fp40: L5.u64_at RSEGS M23 (ref + 40) 2838809733452757089) by (clear - AG23 c22_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp40]).
  assert (c23_Fp48: L5.u64_at RSEGS M23 (ref + 48) 2334102023183623712) by (clear - AG23 c22_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp48]).
  assert (c23_Fp56: L5.u64_at RSEGS M23 (ref + 56) 4188416081412519009) by (clear - AG23 c22_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp56]).
  assert (c23_Fp64w1: L5.u8_at RSEGS M23 (ref + 64) 48) by (clear - AG23 c22_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Fp64w1]).
  assert (c23_Fp65w1: L5.u8_at RSEGS M23 (ref + 65) 0) by (clear - AG23 c22_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M22 M23 _ _ _ (AG23 _ 1)); [lia | exact c22_Fp65w1]).
  assert (c23_Fp16w4: L5.u32_at RSEGS M23 (ref + 16) 0) by (clear - AG23 c22_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M22 M23 _ _ _ (AG23 _ 4)); [lia | exact c22_Fp16w4]).
  assert (c23_Fp8: L5.u64_at RSEGS M23 (ref + 8) 41) by (clear - AG23 c22_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp8]).
  assert (c23_Fp0: L5.u64_at RSEGS M23 ref 41) by (clear - AG23 c22_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Fp0]).
  assert (c23_Om8: L5.u64_at RSEGS M23 (A + 120) S) by (clear - AG23 c22_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om8]).
  assert (c23_Om40: L5.u64_at RSEGS M23 (A + 88) (A + 128)) by (clear - AG23 c22_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om40]).
  assert (c23_Om48: L5.u64_at RSEGS M23 (A + 80) 133556) by (clear - AG23 c22_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om48]).
  assert (c23_Om56: L5.u64_at RSEGS M23 (A + 72) 91856) by (clear - AG23 c22_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om56]).
  assert (c23_Om64: L5.u64_at RSEGS M23 (A + 64) 91995) by (clear - AG23 c22_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om64]).
  assert (c23_Om68w4: L5.u32_at RSEGS M23 (A + 60) 1) by (clear - AG23 c22_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M22 M23 _ _ _ (AG23 _ 4)); [lia | exact c22_Om68w4]).
  assert (c23_Om16: L5.u64_at RSEGS M23 (A + 112) 0) by (clear - AG23 c22_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om16]).
  assert (c23_Om120: L5.u64_at RSEGS M23 (A + 8) 1) by (clear - AG23 c22_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om120]).
  assert (c23_Om24: L5.u64_at RSEGS M23 (A + 104) 260436) by (clear - AG23 c22_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om24]).
  assert (c23_Om32: L5.u64_at RSEGS M23 (A + 96) 4849336966747728640) by (clear - AG23 c22_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om32]).
  assert (c23_Om88: L5.u64_at RSEGS M23 (A + 40) 145512) by (clear - AG23 c22_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om88]).
  assert (c23_Om104: L5.u64_at RSEGS M23 (A + 24) 256628) by (clear - AG23 c22_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om104]).
  assert (c23_Om112: L5.u64_at RSEGS M23 (A + 16) 376040) by (clear - AG23 c22_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om112]).
  assert (c23_Om96: L5.u64_at RSEGS M23 (A + 32) 145780) by (clear - AG23 c22_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M22 M23 _ _ _ (AG23 _ 8)); [lia | exact c22_Om96]).
  assert (STAT23: forall a, stat_rd av a -> M23 (Z_to_bv 64 a) = M22 (Z_to_bv 64 a)).
  { clear - FR23 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR23; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M22 M23 gd av uid rnd canary hw ES22 STAT23) as ES23.
  assert (DEF23: L5.defined M23 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR23 | exact DEF22]).
  assert (DEFref_23: L5.defined M23 ref 66) by (eapply L5.defined_grows; [exact GR23 | exact DEFref_22]).
  assert (DEFA_23: L5.defined M23 A 144) by (eapply L5.defined_grows; [exact GR23 | exact DEFA_22]).
  assert (DEFd3_23: L5.defined M23 d3 64) by (eapply L5.defined_grows; [exact GR23 | exact DEFd3_22]).
  assert (DEFd4_23: L5.defined M23 d4 64) by (eapply L5.defined_grows; [exact GR23 | exact DEFd4_22]).
  assert (HH23: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M23 (m_vmmaps model18)).
  { clear - HH22 GR23 FR23 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH22. lia. 2: exact GR23. intros a Ha.
    destruct (in_dec (S - 544) (S - 480) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR23; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ23: L5C.hpres L LB1 S 10240 XSF M M23).
  { clear - LBWF HQ22 FR23 GR23 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M22 M23 [((S - 544), 64)]). exact LBWF. lia. exact HQ22.
    { intros x Hx. apply FR23; intros Hin.
        apply (Hx ((S - 544), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR23.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG23 FR23 MS23. try clear STAT23. try clear K22.
  try clear c22_Sm488. try clear c22_Sm496. try clear c22_Sm424. try clear c22_Sm432. try clear c22_Sm440. try clear c22_Sm72. try clear c22_Sm80. try clear c22_Sm88. try clear c22_Sm96. try clear c22_Sm104. try clear c22_Sm112. try clear c22_Sm120. try clear c22_Sm128. try clear c22_Sm136. try clear c22_Sm144. try clear c22_Sm152. try clear c22_Sm160. try clear c22_Sm168. try clear c22_Sm24. try clear c22_Sm32. try clear c22_Sm8. try clear c22_Sm16. try clear c22_Sm528w1. try clear c22_Sm472w1. try clear c22_Sm344w1. try clear c22_Sm280w1. try clear c22_Sm248w1. try clear c22_Sm224. try clear c22_Sm232. try clear c22_Sm200w1. try clear c22_Sm176. try clear c22_Sm184. try clear c22_Sm64w1. try clear c22_Om128z8. try clear c22_Om80z12. try clear c22_Op0. try clear c22_Op8. try clear c22_Fp24. try clear c22_Fp32. try clear c22_Fp40. try clear c22_Fp48. try clear c22_Fp56. try clear c22_Fp64w1. try clear c22_Fp65w1. try clear c22_Fp16w4. try clear c22_Fp8. try clear c22_Fp0. try clear c22_Om8. try clear c22_Om40. try clear c22_Om48. try clear c22_Om56. try clear c22_Om64. try clear c22_Om68w4. try clear c22_Om16. try clear c22_Om120. try clear c22_Om24. try clear c22_Om32. try clear c22_Om88. try clear c22_Om104. try clear c22_Om112. try clear c22_Om96. try clear R22_1. try clear R22_2. try clear R22_3. try clear R22_4. try clear R22_8. try clear R22_9. try clear R22_10. try clear R22_11. try clear R22_18. try clear R22_19. try clear R22_20. try clear R22_21. try clear R22_22. try clear R22_23. try clear R22_24. try clear R22_25. try clear R22_26. try clear R22_27. try clear DEF22. try clear HH22. try clear HQ22. try clear ES22. try clear DEFref_22. try clear DEFA_22. try clear DEFd3_22. try clear DEFd4_22.
  (* [comment removed for export] *)
  pose proof ES23 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M23 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r4u_conc fx23 R23 M23 (S - 1008) (A + 128) av canary uid rnd hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx24 & R24 & M24 & MS24 & K24 & R24_1 & R24_2 & R24_8 & R24_9 & R24_10 & R24_11 & FR24 & GR24).
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
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF23 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF23); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF23 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF23); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_23 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_23); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_23 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_23); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c23_Om16 | cellfix c23_Om16]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c23_Om8 | cellfix c23_Om8]. }
  { (* [comment removed for export] *) first [exact c23_Om32 | cellfix c23_Om32]. }
  { (* [comment removed for export] *) first [exact c23_Sm424 | cellfix c23_Sm424]. }
  { (* [comment removed for export] *) first [exact c23_Sm432 | cellfix c23_Sm432]. }
  { (* [comment removed for export] *) first [exact c23_Sm440 | cellfix c23_Sm440]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS24.
  (* [comment removed for export] *)
  assert (AG24: forall a k, ((a + k <= (S - 8944) \/ (S - 480) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M23 M24 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR24; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R24_1n: getr R24 (reg 1) = Z_to_bv 64 142484) by (rewrite R24_1; f_equal; ring). clear R24_1. rename R24_1n into R24_1.
  assert (R24_2n: getr R24 (reg 2) = Z_to_bv 64 (S - 416)) by (rewrite R24_2; f_equal; ring). clear R24_2. rename R24_2n into R24_2.
  assert (R24_3: getr R24 (reg 3) = Z_to_bv 64 67584) by (kin K24 3%nat; exact R23_3).
  assert (R24_4: getr R24 (reg 4) = Z_to_bv 64 462648) by (kin K24 4%nat; exact R23_4).
  assert (R24_8n: getr R24 (reg 8) = Z_to_bv 64 (S + 64)) by (rewrite R24_8; f_equal; ring). clear R24_8. rename R24_8n into R24_8.
  assert (R24_9n: getr R24 (reg 9) = Z_to_bv 64 (S - 64)) by (rewrite R24_9; f_equal; ring). clear R24_9. rename R24_9n into R24_9.
  assert (R24_10n: getr R24 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R24_10; f_equal; ring). clear R24_10. rename R24_10n into R24_10.
  assert (R24_11n: getr R24 (reg 11) = Z_to_bv 64 0) by (rewrite R24_11; f_equal; ring). clear R24_11. rename R24_11n into R24_11.
  assert (R24_18: getr R24 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K24 18%nat; exact R23_18).
  assert (R24_19: getr R24 (reg 19) = Z_to_bv 64 w568) by (kin K24 19%nat; exact R23_19).
  assert (R24_20: getr R24 (reg 20) = Z_to_bv 64 w576) by (kin K24 20%nat; exact R23_20).
  assert (R24_21: getr R24 (reg 21) = Z_to_bv 64 w584) by (kin K24 21%nat; exact R23_21).
  assert (R24_22: getr R24 (reg 22) = Z_to_bv 64 w592) by (kin K24 22%nat; exact R23_22).
  assert (R24_23: getr R24 (reg 23) = Z_to_bv 64 w600) by (kin K24 23%nat; exact R23_23).
  assert (R24_24: getr R24 (reg 24) = Z_to_bv 64 w608) by (kin K24 24%nat; exact R23_24).
  assert (R24_25: getr R24 (reg 25) = Z_to_bv 64 w616) by (kin K24 25%nat; exact R23_25).
  assert (R24_26: getr R24 (reg 26) = Z_to_bv 64 w624) by (kin K24 26%nat; exact R23_26).
  assert (R24_27: getr R24 (reg 27) = Z_to_bv 64 w632) by (kin K24 27%nat; exact R23_27).
  assert (c24_Sm424: L5.u64_at RSEGS M24 (S - 424) 141856) by (clear - AG24 c23_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm424]).
  assert (c24_Sm432: L5.u64_at RSEGS M24 (S - 432) (S + 64)) by (clear - AG24 c23_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm432]).
  assert (c24_Sm440: L5.u64_at RSEGS M24 (S - 440) (S - 64)) by (clear - AG24 c23_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm440]).
  assert (c24_Sm72: L5.u64_at RSEGS M24 (S - 72) 140436) by (clear - AG24 c23_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm72]).
  assert (c24_Sm80: L5.u64_at RSEGS M24 (S - 80) (S + 64)) by (clear - AG24 c23_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm80]).
  assert (c24_Sm88: L5.u64_at RSEGS M24 (S - 88) (U R0 9)) by (clear - AG24 c23_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm88]).
  assert (c24_Sm96: L5.u64_at RSEGS M24 (S - 96) (U R0 18)) by (clear - AG24 c23_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm96]).
  assert (c24_Sm104: L5.u64_at RSEGS M24 (S - 104) (U R0 19)) by (clear - AG24 c23_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm104]).
  assert (c24_Sm112: L5.u64_at RSEGS M24 (S - 112) (U R0 20)) by (clear - AG24 c23_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm112]).
  assert (c24_Sm120: L5.u64_at RSEGS M24 (S - 120) (U R0 21)) by (clear - AG24 c23_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm120]).
  assert (c24_Sm128: L5.u64_at RSEGS M24 (S - 128) (U R0 22)) by (clear - AG24 c23_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm128]).
  assert (c24_Sm136: L5.u64_at RSEGS M24 (S - 136) (U R0 23)) by (clear - AG24 c23_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm136]).
  assert (c24_Sm144: L5.u64_at RSEGS M24 (S - 144) (U R0 24)) by (clear - AG24 c23_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm144]).
  assert (c24_Sm152: L5.u64_at RSEGS M24 (S - 152) (U R0 25)) by (clear - AG24 c23_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm152]).
  assert (c24_Sm160: L5.u64_at RSEGS M24 (S - 160) (U R0 26)) by (clear - AG24 c23_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm160]).
  assert (c24_Sm168: L5.u64_at RSEGS M24 (S - 168) (U R0 27)) by (clear - AG24 c23_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm168]).
  assert (c24_Sm24: L5.u64_at RSEGS M24 (S - 24) 134416) by (clear - AG24 c23_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm24]).
  assert (c24_Sm32: L5.u64_at RSEGS M24 (S - 32) (S + 96)) by (clear - AG24 c23_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm32]).
  assert (c24_Sm8: L5.u64_at RSEGS M24 (S - 8) 133204) by (clear - AG24 c23_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm8]).
  assert (c24_Sm16: L5.u64_at RSEGS M24 (S - 16) (U R0 8)) by (clear - AG24 c23_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm16]).
  assert (c24_Sm472w1: L5.u8_at RSEGS M24 (S - 472) fb472) by (clear - AG24 c23_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm472w1]).
  assert (c24_Sm344w1: L5.u8_at RSEGS M24 (S - 344) fb344) by (clear - AG24 c23_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm344w1]).
  assert (c24_Sm280w1: L5.u8_at RSEGS M24 (S - 280) fb280) by (clear - AG24 c23_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm280w1]).
  assert (c24_Sm248w1: L5.u8_at RSEGS M24 (S - 248) fb248) by (clear - AG24 c23_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm248w1]).
  assert (c24_Sm224: L5.u64_at RSEGS M24 (S - 224) d3) by (clear - AG24 c23_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm224]).
  assert (c24_Sm232: L5.u64_at RSEGS M24 (S - 232) 8) by (clear - AG24 c23_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm232]).
  assert (c24_Sm200w1: L5.u8_at RSEGS M24 (S - 200) fb200) by (clear - AG24 c23_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm200w1]).
  assert (c24_Sm176: L5.u64_at RSEGS M24 (S - 176) d4) by (clear - AG24 c23_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm176]).
  assert (c24_Sm184: L5.u64_at RSEGS M24 (S - 184) 8) by (clear - AG24 c23_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Sm184]).
  assert (c24_Sm64w1: L5.u8_at RSEGS M24 (S - 64) fb64) by (clear - AG24 c23_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Sm64w1]).
  assert (c24_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M24 (A + i) 0)) by (clear - AG24 c23_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | apply c23_Om128z8; exact Hi]).
  assert (c24_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M24 ((A + 48) + i) 0)) by (clear - AG24 c23_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | apply c23_Om80z12; exact Hi]).
  assert (c24_Op0: L5.u64_at RSEGS M24 (A + 128) 376080) by (clear - AG24 c23_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Op0]).
  assert (c24_Op8: L5.u64_at RSEGS M24 (A + 136) (ref + 24)) by (clear - AG24 c23_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Op8]).
  assert (c24_Fp24: L5.u64_at RSEGS M24 (ref + 24) 8028075845441778529) by (clear - AG24 c23_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp24]).
  assert (c24_Fp32: L5.u64_at RSEGS M24 (ref + 32) 7863351059373564014) by (clear - AG24 c23_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp32]).
  assert (c24_Fp40: L5.u64_at RSEGS M24 (ref + 40) 2838809733452757089) by (clear - AG24 c23_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp40]).
  assert (c24_Fp48: L5.u64_at RSEGS M24 (ref + 48) 2334102023183623712) by (clear - AG24 c23_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp48]).
  assert (c24_Fp56: L5.u64_at RSEGS M24 (ref + 56) 4188416081412519009) by (clear - AG24 c23_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp56]).
  assert (c24_Fp64w1: L5.u8_at RSEGS M24 (ref + 64) 48) by (clear - AG24 c23_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Fp64w1]).
  assert (c24_Fp65w1: L5.u8_at RSEGS M24 (ref + 65) 0) by (clear - AG24 c23_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M23 M24 _ _ _ (AG24 _ 1)); [lia | exact c23_Fp65w1]).
  assert (c24_Fp16w4: L5.u32_at RSEGS M24 (ref + 16) 0) by (clear - AG24 c23_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M23 M24 _ _ _ (AG24 _ 4)); [lia | exact c23_Fp16w4]).
  assert (c24_Fp8: L5.u64_at RSEGS M24 (ref + 8) 41) by (clear - AG24 c23_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp8]).
  assert (c24_Fp0: L5.u64_at RSEGS M24 ref 41) by (clear - AG24 c23_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Fp0]).
  assert (c24_Om8: L5.u64_at RSEGS M24 (A + 120) S) by (clear - AG24 c23_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om8]).
  assert (c24_Om40: L5.u64_at RSEGS M24 (A + 88) (A + 128)) by (clear - AG24 c23_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om40]).
  assert (c24_Om48: L5.u64_at RSEGS M24 (A + 80) 133556) by (clear - AG24 c23_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om48]).
  assert (c24_Om56: L5.u64_at RSEGS M24 (A + 72) 91856) by (clear - AG24 c23_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om56]).
  assert (c24_Om64: L5.u64_at RSEGS M24 (A + 64) 91995) by (clear - AG24 c23_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om64]).
  assert (c24_Om68w4: L5.u32_at RSEGS M24 (A + 60) 1) by (clear - AG24 c23_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M23 M24 _ _ _ (AG24 _ 4)); [lia | exact c23_Om68w4]).
  assert (c24_Om16: L5.u64_at RSEGS M24 (A + 112) 0) by (clear - AG24 c23_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om16]).
  assert (c24_Om120: L5.u64_at RSEGS M24 (A + 8) 1) by (clear - AG24 c23_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om120]).
  assert (c24_Om24: L5.u64_at RSEGS M24 (A + 104) 260436) by (clear - AG24 c23_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om24]).
  assert (c24_Om32: L5.u64_at RSEGS M24 (A + 96) 4849336966747728640) by (clear - AG24 c23_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om32]).
  assert (c24_Om88: L5.u64_at RSEGS M24 (A + 40) 145512) by (clear - AG24 c23_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om88]).
  assert (c24_Om104: L5.u64_at RSEGS M24 (A + 24) 256628) by (clear - AG24 c23_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om104]).
  assert (c24_Om112: L5.u64_at RSEGS M24 (A + 16) 376040) by (clear - AG24 c23_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om112]).
  assert (c24_Om96: L5.u64_at RSEGS M24 (A + 32) 145780) by (clear - AG24 c23_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M23 M24 _ _ _ (AG24 _ 8)); [lia | exact c23_Om96]).
  assert (STAT24: forall a, stat_rd av a -> M24 (Z_to_bv 64 a) = M23 (Z_to_bv 64 a)).
  { clear - FR24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR24; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M23 M24 gd av uid rnd canary hw ES23 STAT24) as ES24.
  assert (DEF24: L5.defined M24 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR24 | exact DEF23]).
  assert (DEFref_24: L5.defined M24 ref 66) by (eapply L5.defined_grows; [exact GR24 | exact DEFref_23]).
  assert (DEFA_24: L5.defined M24 A 144) by (eapply L5.defined_grows; [exact GR24 | exact DEFA_23]).
  assert (DEFd3_24: L5.defined M24 d3 64) by (eapply L5.defined_grows; [exact GR24 | exact DEFd3_23]).
  assert (DEFd4_24: L5.defined M24 d4 64) by (eapply L5.defined_grows; [exact GR24 | exact DEFd4_23]).
  assert (HH24: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M24 (m_vmmaps model18)).
  { clear - HH23 GR24 FR24 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH23. lia. 2: exact GR24. intros a Ha.
    destruct (in_dec (S - 8944) (S - 480) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR24; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ24: L5C.hpres L LB1 S 10240 XSF M M24).
  { clear - LBWF HQ23 FR24 GR24 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M23 M24 [((S - 8944), 8464)]). exact LBWF. lia. exact HQ23.
    { intros x Hx. apply FR24; intros Hin.
        apply (Hx ((S - 8944), 8464)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR24.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG24 FR24 MS24. try clear STAT24. try clear K23.
  try clear c23_Sm424. try clear c23_Sm432. try clear c23_Sm440. try clear c23_Sm72. try clear c23_Sm80. try clear c23_Sm88. try clear c23_Sm96. try clear c23_Sm104. try clear c23_Sm112. try clear c23_Sm120. try clear c23_Sm128. try clear c23_Sm136. try clear c23_Sm144. try clear c23_Sm152. try clear c23_Sm160. try clear c23_Sm168. try clear c23_Sm24. try clear c23_Sm32. try clear c23_Sm8. try clear c23_Sm16. try clear c23_Sm472w1. try clear c23_Sm344w1. try clear c23_Sm280w1. try clear c23_Sm248w1. try clear c23_Sm224. try clear c23_Sm232. try clear c23_Sm200w1. try clear c23_Sm176. try clear c23_Sm184. try clear c23_Sm64w1. try clear c23_Om128z8. try clear c23_Om80z12. try clear c23_Op0. try clear c23_Op8. try clear c23_Fp24. try clear c23_Fp32. try clear c23_Fp40. try clear c23_Fp48. try clear c23_Fp56. try clear c23_Fp64w1. try clear c23_Fp65w1. try clear c23_Fp16w4. try clear c23_Fp8. try clear c23_Fp0. try clear c23_Om8. try clear c23_Om40. try clear c23_Om48. try clear c23_Om56. try clear c23_Om64. try clear c23_Om68w4. try clear c23_Om16. try clear c23_Om120. try clear c23_Om24. try clear c23_Om32. try clear c23_Om88. try clear c23_Om104. try clear c23_Om112. try clear c23_Om96. try clear R23_1. try clear R23_2. try clear R23_3. try clear R23_4. try clear R23_8. try clear R23_9. try clear R23_10. try clear R23_11. try clear R23_18. try clear R23_19. try clear R23_20. try clear R23_21. try clear R23_22. try clear R23_23. try clear R23_24. try clear R23_25. try clear R23_26. try clear R23_27. try clear DEF23. try clear HH23. try clear HQ23. try clear ES23. try clear DEFref_23. try clear DEFA_23. try clear DEFd3_23. try clear DEFd4_23.
  eapply (seg14 fx24 R0 R R24 M M24 model model18 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 R24_1 R24_2 R24_3 R24_4 R24_8 R24_9 R24_10 R24_11 R24_18 R24_19 R24_20 R24_21 R24_22 R24_23 R24_24 R24_25 R24_26 R24_27 c24_Sm424 c24_Sm432 c24_Sm440 c24_Sm72 c24_Sm80 c24_Sm88 c24_Sm96 c24_Sm104 c24_Sm112 c24_Sm120 c24_Sm128 c24_Sm136 c24_Sm144 c24_Sm152 c24_Sm160 c24_Sm168 c24_Sm24 c24_Sm32 c24_Sm8 c24_Sm16 c24_Sm472w1 c24_Sm344w1 c24_Sm280w1 c24_Sm248w1 c24_Sm224 c24_Sm232 c24_Sm200w1 c24_Sm176 c24_Sm184 c24_Sm64w1 c24_Om128z8 c24_Om80z12 c24_Op0 c24_Op8 c24_Fp24 c24_Fp32 c24_Fp40 c24_Fp48 c24_Fp56 c24_Fp64w1 c24_Fp65w1 c24_Fp16w4 c24_Fp8 c24_Fp0 c24_Om8 c24_Om40 c24_Om48 c24_Om56 c24_Om64 c24_Om68w4 c24_Om16 c24_Om120 c24_Om24 c24_Om32 c24_Om88 c24_Om104 c24_Om112 c24_Om96 ES24 DEF24 DEFref_24 DEFA_24 DEFd3_24 DEFd4_24 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH24 MOK18 MBV18 HQ24 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3US13.
