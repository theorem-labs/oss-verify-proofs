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
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3AU L5E3T0U L5E3T1U L5E3PU L5E3R1U L5E3R2U L5E3US11.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3US10.
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
Let seg11 := L5E3US11.seg11 L HI LY LYX HIok.

Lemma seg10 (fx15 : FPState) (R0 R R16 : bvmap 5 word) (M M16 : word -> option byte) (model model16 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A ref u3_20 u3_19 : Z) :
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
  0 <= u3_20 < 2 ^ 64 ->
  0 <= u3_19 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R16 (reg 2) = Z_to_bv 64 (S - 880) ->
  (* [comment removed for export] *) getr R16 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R16 (reg 4) = Z_to_bv 64 462648 ->
  (* [comment removed for export] *) getr R16 (reg 8) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R16 (reg 9) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R16 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R16 (reg 19) = Z_to_bv 64 u3_19 ->
  (* [comment removed for export] *) getr R16 (reg 20) = Z_to_bv 64 u3_20 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 536) 144836 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 544) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 560) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 576) w576 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 584) w584 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 592) w592 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 600) w600 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 608) w608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 616) w616 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 624) w624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 632) w632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 488) 143756 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 424) 141856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 440) (S - 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 72) 140436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 80) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 88) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 96) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 104) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 112) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 120) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 128) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 136) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 144) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 152) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 160) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 168) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 24) 134416 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 32) (S + 96) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 8) 133204 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 808) fb808 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 744) fb744 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 720) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 728) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 712) fb712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 688) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 696) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 528) fb528 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 472) fb472 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 344) fb344 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 224) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 232) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 200) fb200 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 176) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (S - 184) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (S - 64) fb64 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M16 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M16 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 128) 376080 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M16 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M16 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 80) 133556 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 72) 91856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 64) 91995 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M16 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 104) 260436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 40) 145512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 24) 256628 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 16) 376040 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M16 (A + 32) 145780 ->
  (* [comment removed for export] *) L5USU.statics_landed M16 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M16 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M16 ref 66 ->
  (* [comment removed for export] *) L5.defined M16 A 144 ->
  (* [comment removed for export] *) L5.defined M16 d2 64 ->
  (* [comment removed for export] *) L5.defined M16 d3 64 ->
  (* [comment removed for export] *) L5.defined M16 d4 64 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d2 \/ d2 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d3 \/ d3 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d4 \/ d4 + 64 <= ref) ->
  (* [comment removed for export] *) (A + 144 <= d2 \/ d2 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d3 \/ d3 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d4 \/ d4 + 64 <= A) ->
  (* [comment removed for export] *) (d2 + 64 <= d3 \/ d3 + 64 <= d2) ->
  (* [comment removed for export] *) (d2 + 64 <= d4 \/ d4 + 64 <= d2) ->
  (* [comment removed for export] *) (d3 + 64 <= d4 \/ d4 + 64 <= d3) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M16 (m_vmmaps model16) ->
  (* [comment removed for export] *) model_ok model16 ->
  (* [comment removed for export] *) model_but_vm model model16 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M16 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5USU.e3_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133556 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx15 R16 142556 M16 model16) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 Wu3_20 Wu3_19 R16_2 R16_3 R16_4 R16_8 R16_9 R16_18 R16_19 R16_20 c16_Sm536 c16_Sm544 c16_Sm552 c16_Sm560 c16_Sm568 c16_Sm576 c16_Sm584 c16_Sm592 c16_Sm600 c16_Sm608 c16_Sm616 c16_Sm624 c16_Sm632 c16_Sm488 c16_Sm496 c16_Sm424 c16_Sm432 c16_Sm440 c16_Sm72 c16_Sm80 c16_Sm88 c16_Sm96 c16_Sm104 c16_Sm112 c16_Sm120 c16_Sm128 c16_Sm136 c16_Sm144 c16_Sm152 c16_Sm160 c16_Sm168 c16_Sm24 c16_Sm32 c16_Sm8 c16_Sm16 c16_Sm808w1 c16_Sm744w1 c16_Sm720 c16_Sm728 c16_Sm712w1 c16_Sm688 c16_Sm696 c16_Sm664w1 c16_Sm528w1 c16_Sm472w1 c16_Sm344w1 c16_Sm280w1 c16_Sm248w1 c16_Sm224 c16_Sm232 c16_Sm200w1 c16_Sm176 c16_Sm184 c16_Sm64w1 c16_Om128z8 c16_Om80z12 c16_Op0 c16_Op8 c16_Fp24 c16_Fp32 c16_Fp40 c16_Fp48 c16_Fp56 c16_Fp64w1 c16_Fp65w1 c16_Fp16w4 c16_Fp8 c16_Fp0 c16_Om8 c16_Om40 c16_Om48 c16_Om56 c16_Om64 c16_Om68w4 c16_Om16 c16_Om120 c16_Om24 c16_Om32 c16_Om88 c16_Om104 c16_Om112 c16_Om96 ES16 DEF16 DEFref_16 DEFA_16 DEFd2_16 DEFd3_16 DEFd4_16 BR_ref BR_A BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d2 AP_A_d3 AP_A_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH16 MOK16 MBV16 HQ16 KE.
  pose proof MOK16 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES16 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 1008) mod 16 = 0). { clear - A16. replace (S - 1008) with (S + (-63) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  set (u16_10 := U R16 10). assert (Wu16_10: 0 <= u16_10 < 2 ^ 64) by (unfold u16_10, U; apply wrange).
  assert (R16_10: getr R16 (reg 10) = Z_to_bv 64 u16_10) by (unfold u16_10, U; symmetry; apply lit_of_word). clearbody u16_10.
  pose proof ES16 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M16 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p2bu_conc fx15 R16 M16 (S - 1008) (A + 128) u16_10 fb712 d2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx17 & R17 & M17 & MS17 & K17 & R17_1 & R17_2 & R17_10 & R17_11 & FR17 & GR17).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu16_10. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb712. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF16); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF16); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_16); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_16); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d2 B1_d2 B3_d2 B4_d2 AP_A_d2. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb712. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite lor1_land254_bit1 by (assumption || kl). first [exact c16_Sm712w1 | cellfix c16_Sm712w1]. }
  { (* [comment removed for export] *) first [exact c16_Sm688 | cellfix c16_Sm688]. }
  { (* [comment removed for export] *) first [exact c16_Sm696 | cellfix c16_Sm696]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS17.
  (* [comment removed for export] *)
  assert (AG17: forall a k, ((a + k <= (S - 944) \/ (S - 880) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M16 M17 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR17; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R17_1n: getr R17 (reg 1) = Z_to_bv 64 142588) by (rewrite R17_1; f_equal; ring). clear R17_1. rename R17_1n into R17_1.
  assert (R17_2n: getr R17 (reg 2) = Z_to_bv 64 (S - 880)) by (rewrite R17_2; f_equal; ring). clear R17_2. rename R17_2n into R17_2.
  assert (R17_3: getr R17 (reg 3) = Z_to_bv 64 67584) by (kin K17 3%nat; exact R16_3).
  assert (R17_4: getr R17 (reg 4) = Z_to_bv 64 462648) by (kin K17 4%nat; exact R16_4).
  assert (R17_8: getr R17 (reg 8) = Z_to_bv 64 (A + 96)) by (kin K17 8%nat; exact R16_8).
  assert (R17_9: getr R17 (reg 9) = Z_to_bv 64 (S + 64)) by (kin K17 9%nat; exact R16_9).
  assert (R17_10n: getr R17 (reg 10) = Z_to_bv 64 d2) by (rewrite R17_10; f_equal; ring). clear R17_10. rename R17_10n into R17_10.
  assert (R17_11n: getr R17 (reg 11) = Z_to_bv 64 64) by (rewrite R17_11; f_equal; ring). clear R17_11. rename R17_11n into R17_11.
  assert (R17_18: getr R17 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K17 18%nat; exact R16_18).
  assert (R17_19: getr R17 (reg 19) = Z_to_bv 64 u3_19) by (kin K17 19%nat; exact R16_19).
  assert (R17_20: getr R17 (reg 20) = Z_to_bv 64 u3_20) by (kin K17 20%nat; exact R16_20).
  assert (c17_Sm536: L5.u64_at RSEGS M17 (S - 536) 144836) by (clear - AG17 c16_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm536]).
  assert (c17_Sm544: L5.u64_at RSEGS M17 (S - 544) (S + 64)) by (clear - AG17 c16_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm544]).
  assert (c17_Sm552: L5.u64_at RSEGS M17 (S - 552) w552) by (clear - AG17 c16_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm552]).
  assert (c17_Sm560: L5.u64_at RSEGS M17 (S - 560) (S + 64)) by (clear - AG17 c16_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm560]).
  assert (c17_Sm568: L5.u64_at RSEGS M17 (S - 568) w568) by (clear - AG17 c16_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm568]).
  assert (c17_Sm576: L5.u64_at RSEGS M17 (S - 576) w576) by (clear - AG17 c16_Sm576 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm576]).
  assert (c17_Sm584: L5.u64_at RSEGS M17 (S - 584) w584) by (clear - AG17 c16_Sm584 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm584]).
  assert (c17_Sm592: L5.u64_at RSEGS M17 (S - 592) w592) by (clear - AG17 c16_Sm592 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm592]).
  assert (c17_Sm600: L5.u64_at RSEGS M17 (S - 600) w600) by (clear - AG17 c16_Sm600 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm600]).
  assert (c17_Sm608: L5.u64_at RSEGS M17 (S - 608) w608) by (clear - AG17 c16_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm608]).
  assert (c17_Sm616: L5.u64_at RSEGS M17 (S - 616) w616) by (clear - AG17 c16_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm616]).
  assert (c17_Sm624: L5.u64_at RSEGS M17 (S - 624) w624) by (clear - AG17 c16_Sm624 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm624]).
  assert (c17_Sm632: L5.u64_at RSEGS M17 (S - 632) w632) by (clear - AG17 c16_Sm632 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm632]).
  assert (c17_Sm488: L5.u64_at RSEGS M17 (S - 488) 143756) by (clear - AG17 c16_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm488]).
  assert (c17_Sm496: L5.u64_at RSEGS M17 (S - 496) (S + 64)) by (clear - AG17 c16_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm496]).
  assert (c17_Sm424: L5.u64_at RSEGS M17 (S - 424) 141856) by (clear - AG17 c16_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm424]).
  assert (c17_Sm432: L5.u64_at RSEGS M17 (S - 432) (S + 64)) by (clear - AG17 c16_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm432]).
  assert (c17_Sm440: L5.u64_at RSEGS M17 (S - 440) (S - 64)) by (clear - AG17 c16_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm440]).
  assert (c17_Sm72: L5.u64_at RSEGS M17 (S - 72) 140436) by (clear - AG17 c16_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm72]).
  assert (c17_Sm80: L5.u64_at RSEGS M17 (S - 80) (S + 64)) by (clear - AG17 c16_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm80]).
  assert (c17_Sm88: L5.u64_at RSEGS M17 (S - 88) (U R0 9)) by (clear - AG17 c16_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm88]).
  assert (c17_Sm96: L5.u64_at RSEGS M17 (S - 96) (U R0 18)) by (clear - AG17 c16_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm96]).
  assert (c17_Sm104: L5.u64_at RSEGS M17 (S - 104) (U R0 19)) by (clear - AG17 c16_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm104]).
  assert (c17_Sm112: L5.u64_at RSEGS M17 (S - 112) (U R0 20)) by (clear - AG17 c16_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm112]).
  assert (c17_Sm120: L5.u64_at RSEGS M17 (S - 120) (U R0 21)) by (clear - AG17 c16_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm120]).
  assert (c17_Sm128: L5.u64_at RSEGS M17 (S - 128) (U R0 22)) by (clear - AG17 c16_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm128]).
  assert (c17_Sm136: L5.u64_at RSEGS M17 (S - 136) (U R0 23)) by (clear - AG17 c16_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm136]).
  assert (c17_Sm144: L5.u64_at RSEGS M17 (S - 144) (U R0 24)) by (clear - AG17 c16_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm144]).
  assert (c17_Sm152: L5.u64_at RSEGS M17 (S - 152) (U R0 25)) by (clear - AG17 c16_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm152]).
  assert (c17_Sm160: L5.u64_at RSEGS M17 (S - 160) (U R0 26)) by (clear - AG17 c16_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm160]).
  assert (c17_Sm168: L5.u64_at RSEGS M17 (S - 168) (U R0 27)) by (clear - AG17 c16_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm168]).
  assert (c17_Sm24: L5.u64_at RSEGS M17 (S - 24) 134416) by (clear - AG17 c16_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm24]).
  assert (c17_Sm32: L5.u64_at RSEGS M17 (S - 32) (S + 96)) by (clear - AG17 c16_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm32]).
  assert (c17_Sm8: L5.u64_at RSEGS M17 (S - 8) 133204) by (clear - AG17 c16_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm8]).
  assert (c17_Sm16: L5.u64_at RSEGS M17 (S - 16) (U R0 8)) by (clear - AG17 c16_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm16]).
  assert (c17_Sm808w1: L5.u8_at RSEGS M17 (S - 808) fb808) by (clear - AG17 c16_Sm808w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm808w1]).
  assert (c17_Sm744w1: L5.u8_at RSEGS M17 (S - 744) fb744) by (clear - AG17 c16_Sm744w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm744w1]).
  assert (c17_Sm720: L5.u64_at RSEGS M17 (S - 720) d1) by (clear - AG17 c16_Sm720 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm720]).
  assert (c17_Sm728: L5.u64_at RSEGS M17 (S - 728) 8) by (clear - AG17 c16_Sm728 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm728]).
  assert (c17_Sm712w1: L5.u8_at RSEGS M17 (S - 712) fb712) by (clear - AG17 c16_Sm712w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm712w1]).
  assert (c17_Sm688: L5.u64_at RSEGS M17 (S - 688) d2) by (clear - AG17 c16_Sm688 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm688]).
  assert (c17_Sm696: L5.u64_at RSEGS M17 (S - 696) 8) by (clear - AG17 c16_Sm696 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm696]).
  assert (c17_Sm664w1: L5.u8_at RSEGS M17 (S - 664) fb664) by (clear - AG17 c16_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm664w1]).
  assert (c17_Sm528w1: L5.u8_at RSEGS M17 (S - 528) fb528) by (clear - AG17 c16_Sm528w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm528w1]).
  assert (c17_Sm472w1: L5.u8_at RSEGS M17 (S - 472) fb472) by (clear - AG17 c16_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm472w1]).
  assert (c17_Sm344w1: L5.u8_at RSEGS M17 (S - 344) fb344) by (clear - AG17 c16_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm344w1]).
  assert (c17_Sm280w1: L5.u8_at RSEGS M17 (S - 280) fb280) by (clear - AG17 c16_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm280w1]).
  assert (c17_Sm248w1: L5.u8_at RSEGS M17 (S - 248) fb248) by (clear - AG17 c16_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm248w1]).
  assert (c17_Sm224: L5.u64_at RSEGS M17 (S - 224) d3) by (clear - AG17 c16_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm224]).
  assert (c17_Sm232: L5.u64_at RSEGS M17 (S - 232) 8) by (clear - AG17 c16_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm232]).
  assert (c17_Sm200w1: L5.u8_at RSEGS M17 (S - 200) fb200) by (clear - AG17 c16_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm200w1]).
  assert (c17_Sm176: L5.u64_at RSEGS M17 (S - 176) d4) by (clear - AG17 c16_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm176]).
  assert (c17_Sm184: L5.u64_at RSEGS M17 (S - 184) 8) by (clear - AG17 c16_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Sm184]).
  assert (c17_Sm64w1: L5.u8_at RSEGS M17 (S - 64) fb64) by (clear - AG17 c16_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Sm64w1]).
  assert (c17_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M17 (A + i) 0)) by (clear - AG17 c16_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | apply c16_Om128z8; exact Hi]).
  assert (c17_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M17 ((A + 48) + i) 0)) by (clear - AG17 c16_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | apply c16_Om80z12; exact Hi]).
  assert (c17_Op0: L5.u64_at RSEGS M17 (A + 128) 376080) by (clear - AG17 c16_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Op0]).
  assert (c17_Op8: L5.u64_at RSEGS M17 (A + 136) (ref + 24)) by (clear - AG17 c16_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Op8]).
  assert (c17_Fp24: L5.u64_at RSEGS M17 (ref + 24) 8028075845441778529) by (clear - AG17 c16_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp24]).
  assert (c17_Fp32: L5.u64_at RSEGS M17 (ref + 32) 7863351059373564014) by (clear - AG17 c16_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp32]).
  assert (c17_Fp40: L5.u64_at RSEGS M17 (ref + 40) 2838809733452757089) by (clear - AG17 c16_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp40]).
  assert (c17_Fp48: L5.u64_at RSEGS M17 (ref + 48) 2334102023183623712) by (clear - AG17 c16_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp48]).
  assert (c17_Fp56: L5.u64_at RSEGS M17 (ref + 56) 4188416081412519009) by (clear - AG17 c16_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp56]).
  assert (c17_Fp64w1: L5.u8_at RSEGS M17 (ref + 64) 48) by (clear - AG17 c16_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Fp64w1]).
  assert (c17_Fp65w1: L5.u8_at RSEGS M17 (ref + 65) 0) by (clear - AG17 c16_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M16 M17 _ _ _ (AG17 _ 1)); [lia | exact c16_Fp65w1]).
  assert (c17_Fp16w4: L5.u32_at RSEGS M17 (ref + 16) 0) by (clear - AG17 c16_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M16 M17 _ _ _ (AG17 _ 4)); [lia | exact c16_Fp16w4]).
  assert (c17_Fp8: L5.u64_at RSEGS M17 (ref + 8) 41) by (clear - AG17 c16_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp8]).
  assert (c17_Fp0: L5.u64_at RSEGS M17 ref 41) by (clear - AG17 c16_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Fp0]).
  assert (c17_Om8: L5.u64_at RSEGS M17 (A + 120) S) by (clear - AG17 c16_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om8]).
  assert (c17_Om40: L5.u64_at RSEGS M17 (A + 88) (A + 128)) by (clear - AG17 c16_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om40]).
  assert (c17_Om48: L5.u64_at RSEGS M17 (A + 80) 133556) by (clear - AG17 c16_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om48]).
  assert (c17_Om56: L5.u64_at RSEGS M17 (A + 72) 91856) by (clear - AG17 c16_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om56]).
  assert (c17_Om64: L5.u64_at RSEGS M17 (A + 64) 91995) by (clear - AG17 c16_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om64]).
  assert (c17_Om68w4: L5.u32_at RSEGS M17 (A + 60) 1) by (clear - AG17 c16_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M16 M17 _ _ _ (AG17 _ 4)); [lia | exact c16_Om68w4]).
  assert (c17_Om16: L5.u64_at RSEGS M17 (A + 112) 0) by (clear - AG17 c16_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om16]).
  assert (c17_Om120: L5.u64_at RSEGS M17 (A + 8) 1) by (clear - AG17 c16_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om120]).
  assert (c17_Om24: L5.u64_at RSEGS M17 (A + 104) 260436) by (clear - AG17 c16_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om24]).
  assert (c17_Om32: L5.u64_at RSEGS M17 (A + 96) 4849336966747728640) by (clear - AG17 c16_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om32]).
  assert (c17_Om88: L5.u64_at RSEGS M17 (A + 40) 145512) by (clear - AG17 c16_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om88]).
  assert (c17_Om104: L5.u64_at RSEGS M17 (A + 24) 256628) by (clear - AG17 c16_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om104]).
  assert (c17_Om112: L5.u64_at RSEGS M17 (A + 16) 376040) by (clear - AG17 c16_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om112]).
  assert (c17_Om96: L5.u64_at RSEGS M17 (A + 32) 145780) by (clear - AG17 c16_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M16 M17 _ _ _ (AG17 _ 8)); [lia | exact c16_Om96]).
  assert (STAT17: forall a, stat_rd av a -> M17 (Z_to_bv 64 a) = M16 (Z_to_bv 64 a)).
  { clear - FR17 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR17; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M16 M17 gd av uid rnd canary hw ES16 STAT17) as ES17.
  assert (DEF17: L5.defined M17 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR17 | exact DEF16]).
  assert (DEFref_17: L5.defined M17 ref 66) by (eapply L5.defined_grows; [exact GR17 | exact DEFref_16]).
  assert (DEFA_17: L5.defined M17 A 144) by (eapply L5.defined_grows; [exact GR17 | exact DEFA_16]).
  assert (DEFd2_17: L5.defined M17 d2 64) by (eapply L5.defined_grows; [exact GR17 | exact DEFd2_16]).
  assert (DEFd3_17: L5.defined M17 d3 64) by (eapply L5.defined_grows; [exact GR17 | exact DEFd3_16]).
  assert (DEFd4_17: L5.defined M17 d4 64) by (eapply L5.defined_grows; [exact GR17 | exact DEFd4_16]).
  assert (HH17: hi_heap HI ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M17 (m_vmmaps model16)).
  { clear - HH16 GR17 FR17 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH16. lia. 2: exact GR17. intros a Ha.
    destruct (in_dec (S - 944) (S - 880) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR17; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ17: L5C.hpres L LB1 S 10240 XSF M M17).
  { clear - LBWF HQ16 FR17 GR17 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M16 M17 [((S - 944), 64)]). exact LBWF. lia. exact HQ16.
    { intros x Hx. apply FR17; intros Hin.
        apply (Hx ((S - 944), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR17.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG17 FR17 MS17. try clear STAT17. try clear K16.
  try clear c16_Sm536. try clear c16_Sm544. try clear c16_Sm552. try clear c16_Sm560. try clear c16_Sm568. try clear c16_Sm576. try clear c16_Sm584. try clear c16_Sm592. try clear c16_Sm600. try clear c16_Sm608. try clear c16_Sm616. try clear c16_Sm624. try clear c16_Sm632. try clear c16_Sm488. try clear c16_Sm496. try clear c16_Sm424. try clear c16_Sm432. try clear c16_Sm440. try clear c16_Sm72. try clear c16_Sm80. try clear c16_Sm88. try clear c16_Sm96. try clear c16_Sm104. try clear c16_Sm112. try clear c16_Sm120. try clear c16_Sm128. try clear c16_Sm136. try clear c16_Sm144. try clear c16_Sm152. try clear c16_Sm160. try clear c16_Sm168. try clear c16_Sm24. try clear c16_Sm32. try clear c16_Sm8. try clear c16_Sm16. try clear c16_Sm808w1. try clear c16_Sm744w1. try clear c16_Sm720. try clear c16_Sm728. try clear c16_Sm712w1. try clear c16_Sm688. try clear c16_Sm696. try clear c16_Sm664w1. try clear c16_Sm528w1. try clear c16_Sm472w1. try clear c16_Sm344w1. try clear c16_Sm280w1. try clear c16_Sm248w1. try clear c16_Sm224. try clear c16_Sm232. try clear c16_Sm200w1. try clear c16_Sm176. try clear c16_Sm184. try clear c16_Sm64w1. try clear c16_Om128z8. try clear c16_Om80z12. try clear c16_Op0. try clear c16_Op8. try clear c16_Fp24. try clear c16_Fp32. try clear c16_Fp40. try clear c16_Fp48. try clear c16_Fp56. try clear c16_Fp64w1. try clear c16_Fp65w1. try clear c16_Fp16w4. try clear c16_Fp8. try clear c16_Fp0. try clear c16_Om8. try clear c16_Om40. try clear c16_Om48. try clear c16_Om56. try clear c16_Om64. try clear c16_Om68w4. try clear c16_Om16. try clear c16_Om120. try clear c16_Om24. try clear c16_Om32. try clear c16_Om88. try clear c16_Om104. try clear c16_Om112. try clear c16_Om96. try clear R16_2. try clear R16_3. try clear R16_4. try clear R16_8. try clear R16_9. try clear R16_18. try clear R16_19. try clear R16_20. try clear R16_10. try clear DEF16. try clear HH16. try clear HQ16. try clear ES16. try clear DEFref_16. try clear DEFA_16. try clear DEFd2_16. try clear DEFd3_16. try clear DEFd4_16.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx17 R17 M17 model16 ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) d2 64 K) as HC.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH17.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - right; right; left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R17_10.
  - rewrite L5CoreKit.L5K.rl4. exact R17_4.
  - rewrite L5CoreKit.L5K.rl1, R17_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R17_2 A16 DEF17 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R17_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-55) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M17 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF17. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R18 M18 model18 RP18 [PRES18 _] MBVn HH18.
    rewrite L5CoreKit.L5K.rl1, R17_1.
    cbn [lb_remove fst app] in PRES18, HH18.
    rewrite (proj2 (Z.eqb_neq ref d2) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref B0_d2 B1_d2 B3_d2 B4_d2 AP_ref_d2)) in PRES18, HH18.
    rewrite (proj2 (Z.eqb_neq A d2) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d2 B1_d2 B3_d2 B4_d2 AP_A_d2)) in PRES18, HH18.
    rewrite Z.eqb_refl in PRES18, HH18.
    rewrite L5CoreKit.L5K.rl2, R17_2, BG.unsigned_lit in PRES18 by (kl SLO SHI STOP).
    match type of PRES18 with heap_pres_core _ _ ?x _ _ => replace x with (S - 880) in PRES18 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (S - 880) M17 M18 PRES18) as HP18. rewrite (ly_stack L LY) in HP18. unfold HEAP_STACK in HP18.
    assert (AGS18: forall a k, ((S - 880) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M17 M18 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP18 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP18. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB18_ref: L5C.agree_on M17 M18 ref 66).
    { clear - HP18 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP18. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB18_A: L5C.agree_on M17 M18 A 144).
    { clear - HP18 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP18. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB18_d3: L5C.agree_on M17 M18 d3 64).
    { clear - HP18 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP18. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB18_d4: L5C.agree_on M17 M18 d4 64).
    { clear - HP18 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP18. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT18: forall a, stat_rd av a -> M18 (Z_to_bv 64 a) = M17 (Z_to_bv 64 a)).
    { clear - HP18 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (S - 880) 8224 [] M17 M18 HP18). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (statics_landed_keep M17 M18 gd av uid rnd canary hw ES17 STAT18) as ES18.
    assert (DEF18: L5.defined M18 (S - 10240) 10240).
    { clear - HP18 DEF17 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (S - 880) 8224 [] M17 M18). exact HP18. lia. lia. lia. lia. exact DEF17. }
    assert (DEFref_18: L5.defined M18 ref 66) by (eapply (L5C.defined_agree M17 M18); [exact AGB18_ref | exact DEFref_17]).
    assert (DEFA_18: L5.defined M18 A 144) by (eapply (L5C.defined_agree M17 M18); [exact AGB18_A | exact DEFA_17]).
    assert (DEFd3_18: L5.defined M18 d3 64) by (eapply (L5C.defined_agree M17 M18); [exact AGB18_d3 | exact DEFd3_17]).
    assert (DEFd4_18: L5.defined M18 d4 64) by (eapply (L5C.defined_agree M17 M18); [exact AGB18_d4 | exact DEFd4_17]).
    assert (MOK18: model_ok model18).
    { destruct MOK16 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK18 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV16 MBVn) as MBV18. clear MBVn MBV16.
    assert (RPi18: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R18 (reg i) = getr R17 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R17 R18 i RP18). exact Hi. }
    assert (R18_2: getr R18 (reg 2) = Z_to_bv 64 (S - 880)) by (rewrite (RPi18 2%nat) by inl; exact R17_2).
    assert (R18_3: getr R18 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi18 3%nat) by inl; exact R17_3).
    assert (R18_4: getr R18 (reg 4) = Z_to_bv 64 462648) by (rewrite (RPi18 4%nat) by inl; exact R17_4).
    assert (R18_8: getr R18 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite (RPi18 8%nat) by inl; exact R17_8).
    assert (R18_9: getr R18 (reg 9) = Z_to_bv 64 (S + 64)) by (rewrite (RPi18 9%nat) by inl; exact R17_9).
    assert (R18_18: getr R18 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite (RPi18 18%nat) by inl; exact R17_18).
    assert (R18_19: getr R18 (reg 19) = Z_to_bv 64 u3_19) by (rewrite (RPi18 19%nat) by inl; exact R17_19).
    assert (R18_20: getr R18 (reg 20) = Z_to_bv 64 u3_20) by (rewrite (RPi18 20%nat) by inl; exact R17_20).
    assert (c18_Sm536: L5.u64_at RSEGS M18 (S - 536) 144836) by (clear - AGS18 c17_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm536]).
    assert (c18_Sm544: L5.u64_at RSEGS M18 (S - 544) (S + 64)) by (clear - AGS18 c17_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm544]).
    assert (c18_Sm552: L5.u64_at RSEGS M18 (S - 552) w552) by (clear - AGS18 c17_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm552]).
    assert (c18_Sm560: L5.u64_at RSEGS M18 (S - 560) (S + 64)) by (clear - AGS18 c17_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm560]).
    assert (c18_Sm568: L5.u64_at RSEGS M18 (S - 568) w568) by (clear - AGS18 c17_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm568]).
    assert (c18_Sm576: L5.u64_at RSEGS M18 (S - 576) w576) by (clear - AGS18 c17_Sm576 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm576]).
    assert (c18_Sm584: L5.u64_at RSEGS M18 (S - 584) w584) by (clear - AGS18 c17_Sm584 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm584]).
    assert (c18_Sm592: L5.u64_at RSEGS M18 (S - 592) w592) by (clear - AGS18 c17_Sm592 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm592]).
    assert (c18_Sm600: L5.u64_at RSEGS M18 (S - 600) w600) by (clear - AGS18 c17_Sm600 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm600]).
    assert (c18_Sm608: L5.u64_at RSEGS M18 (S - 608) w608) by (clear - AGS18 c17_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm608]).
    assert (c18_Sm616: L5.u64_at RSEGS M18 (S - 616) w616) by (clear - AGS18 c17_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm616]).
    assert (c18_Sm624: L5.u64_at RSEGS M18 (S - 624) w624) by (clear - AGS18 c17_Sm624 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm624]).
    assert (c18_Sm632: L5.u64_at RSEGS M18 (S - 632) w632) by (clear - AGS18 c17_Sm632 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm632]).
    assert (c18_Sm488: L5.u64_at RSEGS M18 (S - 488) 143756) by (clear - AGS18 c17_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm488]).
    assert (c18_Sm496: L5.u64_at RSEGS M18 (S - 496) (S + 64)) by (clear - AGS18 c17_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm496]).
    assert (c18_Sm424: L5.u64_at RSEGS M18 (S - 424) 141856) by (clear - AGS18 c17_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm424]).
    assert (c18_Sm432: L5.u64_at RSEGS M18 (S - 432) (S + 64)) by (clear - AGS18 c17_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm432]).
    assert (c18_Sm440: L5.u64_at RSEGS M18 (S - 440) (S - 64)) by (clear - AGS18 c17_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm440]).
    assert (c18_Sm72: L5.u64_at RSEGS M18 (S - 72) 140436) by (clear - AGS18 c17_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm72]).
    assert (c18_Sm80: L5.u64_at RSEGS M18 (S - 80) (S + 64)) by (clear - AGS18 c17_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm80]).
    assert (c18_Sm88: L5.u64_at RSEGS M18 (S - 88) (U R0 9)) by (clear - AGS18 c17_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm88]).
    assert (c18_Sm96: L5.u64_at RSEGS M18 (S - 96) (U R0 18)) by (clear - AGS18 c17_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm96]).
    assert (c18_Sm104: L5.u64_at RSEGS M18 (S - 104) (U R0 19)) by (clear - AGS18 c17_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm104]).
    assert (c18_Sm112: L5.u64_at RSEGS M18 (S - 112) (U R0 20)) by (clear - AGS18 c17_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm112]).
    assert (c18_Sm120: L5.u64_at RSEGS M18 (S - 120) (U R0 21)) by (clear - AGS18 c17_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm120]).
    assert (c18_Sm128: L5.u64_at RSEGS M18 (S - 128) (U R0 22)) by (clear - AGS18 c17_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm128]).
    assert (c18_Sm136: L5.u64_at RSEGS M18 (S - 136) (U R0 23)) by (clear - AGS18 c17_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm136]).
    assert (c18_Sm144: L5.u64_at RSEGS M18 (S - 144) (U R0 24)) by (clear - AGS18 c17_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm144]).
    assert (c18_Sm152: L5.u64_at RSEGS M18 (S - 152) (U R0 25)) by (clear - AGS18 c17_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm152]).
    assert (c18_Sm160: L5.u64_at RSEGS M18 (S - 160) (U R0 26)) by (clear - AGS18 c17_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm160]).
    assert (c18_Sm168: L5.u64_at RSEGS M18 (S - 168) (U R0 27)) by (clear - AGS18 c17_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm168]).
    assert (c18_Sm24: L5.u64_at RSEGS M18 (S - 24) 134416) by (clear - AGS18 c17_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm24]).
    assert (c18_Sm32: L5.u64_at RSEGS M18 (S - 32) (S + 96)) by (clear - AGS18 c17_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm32]).
    assert (c18_Sm8: L5.u64_at RSEGS M18 (S - 8) 133204) by (clear - AGS18 c17_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm8]).
    assert (c18_Sm16: L5.u64_at RSEGS M18 (S - 16) (U R0 8)) by (clear - AGS18 c17_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm16]).
    assert (c18_Sm808w1: L5.u8_at RSEGS M18 (S - 808) fb808) by (clear - AGS18 c17_Sm808w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm808w1]).
    assert (c18_Sm744w1: L5.u8_at RSEGS M18 (S - 744) fb744) by (clear - AGS18 c17_Sm744w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm744w1]).
    assert (c18_Sm720: L5.u64_at RSEGS M18 (S - 720) d1) by (clear - AGS18 c17_Sm720 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm720]).
    assert (c18_Sm728: L5.u64_at RSEGS M18 (S - 728) 8) by (clear - AGS18 c17_Sm728 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm728]).
    assert (c18_Sm712w1: L5.u8_at RSEGS M18 (S - 712) fb712) by (clear - AGS18 c17_Sm712w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm712w1]).
    assert (c18_Sm688: L5.u64_at RSEGS M18 (S - 688) d2) by (clear - AGS18 c17_Sm688 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm688]).
    assert (c18_Sm696: L5.u64_at RSEGS M18 (S - 696) 8) by (clear - AGS18 c17_Sm696 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm696]).
    assert (c18_Sm664w1: L5.u8_at RSEGS M18 (S - 664) fb664) by (clear - AGS18 c17_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm664w1]).
    assert (c18_Sm528w1: L5.u8_at RSEGS M18 (S - 528) fb528) by (clear - AGS18 c17_Sm528w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm528w1]).
    assert (c18_Sm472w1: L5.u8_at RSEGS M18 (S - 472) fb472) by (clear - AGS18 c17_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm472w1]).
    assert (c18_Sm344w1: L5.u8_at RSEGS M18 (S - 344) fb344) by (clear - AGS18 c17_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm344w1]).
    assert (c18_Sm280w1: L5.u8_at RSEGS M18 (S - 280) fb280) by (clear - AGS18 c17_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm280w1]).
    assert (c18_Sm248w1: L5.u8_at RSEGS M18 (S - 248) fb248) by (clear - AGS18 c17_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm248w1]).
    assert (c18_Sm224: L5.u64_at RSEGS M18 (S - 224) d3) by (clear - AGS18 c17_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm224]).
    assert (c18_Sm232: L5.u64_at RSEGS M18 (S - 232) 8) by (clear - AGS18 c17_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm232]).
    assert (c18_Sm200w1: L5.u8_at RSEGS M18 (S - 200) fb200) by (clear - AGS18 c17_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm200w1]).
    assert (c18_Sm176: L5.u64_at RSEGS M18 (S - 176) d4) by (clear - AGS18 c17_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm176]).
    assert (c18_Sm184: L5.u64_at RSEGS M18 (S - 184) 8) by (clear - AGS18 c17_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M17 M18 _ _ _ (AGS18 _ 8)); [lia | exact c17_Sm184]).
    assert (c18_Sm64w1: L5.u8_at RSEGS M18 (S - 64) fb64) by (clear - AGS18 c17_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M17 M18 _ _ _ (AGS18 _ 1)); [lia | exact c17_Sm64w1]).
    assert (c18_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M18 (A + i) 0)) by (clear - AGB18_A c17_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB18_A); [lia | apply c17_Om128z8; exact Hi]).
    assert (c18_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M18 ((A + 48) + i) 0)) by (clear - AGB18_A c17_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB18_A); [lia | apply c17_Om80z12; exact Hi]).
    assert (c18_Op0: L5.u64_at RSEGS M18 (A + 128) 376080) by (clear - AGB18_A c17_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Op0]).
    assert (c18_Op8: L5.u64_at RSEGS M18 (A + 136) (ref + 24)) by (clear - AGB18_A c17_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Op8]).
    assert (c18_Fp24: L5.u64_at RSEGS M18 (ref + 24) 8028075845441778529) by (clear - AGB18_ref c17_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp24]).
    assert (c18_Fp32: L5.u64_at RSEGS M18 (ref + 32) 7863351059373564014) by (clear - AGB18_ref c17_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp32]).
    assert (c18_Fp40: L5.u64_at RSEGS M18 (ref + 40) 2838809733452757089) by (clear - AGB18_ref c17_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp40]).
    assert (c18_Fp48: L5.u64_at RSEGS M18 (ref + 48) 2334102023183623712) by (clear - AGB18_ref c17_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp48]).
    assert (c18_Fp56: L5.u64_at RSEGS M18 (ref + 56) 4188416081412519009) by (clear - AGB18_ref c17_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp56]).
    assert (c18_Fp64w1: L5.u8_at RSEGS M18 (ref + 64) 48) by (clear - AGB18_ref c17_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp64w1]).
    assert (c18_Fp65w1: L5.u8_at RSEGS M18 (ref + 65) 0) by (clear - AGB18_ref c17_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp65w1]).
    assert (c18_Fp16w4: L5.u32_at RSEGS M18 (ref + 16) 0) by (clear - AGB18_ref c17_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb32 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp16w4]).
    assert (c18_Fp8: L5.u64_at RSEGS M18 (ref + 8) 41) by (clear - AGB18_ref c17_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp8]).
    assert (c18_Fp0: L5.u64_at RSEGS M18 ref 41) by (clear - AGB18_ref c17_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB18_ref); [lia | exact c17_Fp0]).
    assert (c18_Om8: L5.u64_at RSEGS M18 (A + 120) S) by (clear - AGB18_A c17_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om8]).
    assert (c18_Om40: L5.u64_at RSEGS M18 (A + 88) (A + 128)) by (clear - AGB18_A c17_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om40]).
    assert (c18_Om48: L5.u64_at RSEGS M18 (A + 80) 133556) by (clear - AGB18_A c17_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om48]).
    assert (c18_Om56: L5.u64_at RSEGS M18 (A + 72) 91856) by (clear - AGB18_A c17_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om56]).
    assert (c18_Om64: L5.u64_at RSEGS M18 (A + 64) 91995) by (clear - AGB18_A c17_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om64]).
    assert (c18_Om68w4: L5.u32_at RSEGS M18 (A + 60) 1) by (clear - AGB18_A c17_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb32 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om68w4]).
    assert (c18_Om16: L5.u64_at RSEGS M18 (A + 112) 0) by (clear - AGB18_A c17_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om16]).
    assert (c18_Om120: L5.u64_at RSEGS M18 (A + 8) 1) by (clear - AGB18_A c17_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om120]).
    assert (c18_Om24: L5.u64_at RSEGS M18 (A + 104) 260436) by (clear - AGB18_A c17_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om24]).
    assert (c18_Om32: L5.u64_at RSEGS M18 (A + 96) 4849336966747728640) by (clear - AGB18_A c17_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om32]).
    assert (c18_Om88: L5.u64_at RSEGS M18 (A + 40) 145512) by (clear - AGB18_A c17_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om88]).
    assert (c18_Om104: L5.u64_at RSEGS M18 (A + 24) 256628) by (clear - AGB18_A c17_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om104]).
    assert (c18_Om112: L5.u64_at RSEGS M18 (A + 16) 376040) by (clear - AGB18_A c17_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om112]).
    assert (c18_Om96: L5.u64_at RSEGS M18 (A + 32) 145780) by (clear - AGB18_A c17_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB18_A); [lia | exact c17_Om96]).
    assert (HQ18: L5C.hpres L LB1 S 10240 XSF M M18).
    { clear - LBWF HQ17 HP18 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 880) 8224 [] M M17 M18). exact LBWF. lia. lia. exact HQ17. exact HP18. intros bb Hbb; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS18 STAT18 PRES18 RP18 RPi18 HP18 AGB18_ref AGB18_A AGB18_d3 AGB18_d4.
    try clear c17_Sm536 c17_Sm544 c17_Sm552 c17_Sm560 c17_Sm568 c17_Sm576 c17_Sm584 c17_Sm592 c17_Sm600 c17_Sm608 c17_Sm616 c17_Sm624 c17_Sm632 c17_Sm488 c17_Sm496 c17_Sm424 c17_Sm432 c17_Sm440 c17_Sm72 c17_Sm80 c17_Sm88 c17_Sm96 c17_Sm104 c17_Sm112 c17_Sm120 c17_Sm128 c17_Sm136 c17_Sm144 c17_Sm152 c17_Sm160 c17_Sm168 c17_Sm24 c17_Sm32 c17_Sm8 c17_Sm16 c17_Sm808w1 c17_Sm744w1 c17_Sm720 c17_Sm728 c17_Sm712w1 c17_Sm688 c17_Sm696 c17_Sm664w1 c17_Sm528w1 c17_Sm472w1 c17_Sm344w1 c17_Sm280w1 c17_Sm248w1 c17_Sm224 c17_Sm232 c17_Sm200w1 c17_Sm176 c17_Sm184 c17_Sm64w1 c17_Om128z8 c17_Om80z12 c17_Op0 c17_Op8 c17_Fp24 c17_Fp32 c17_Fp40 c17_Fp48 c17_Fp56 c17_Fp64w1 c17_Fp65w1 c17_Fp16w4 c17_Fp8 c17_Fp0 c17_Om8 c17_Om40 c17_Om48 c17_Om56 c17_Om64 c17_Om68w4 c17_Om16 c17_Om120 c17_Om24 c17_Om32 c17_Om88 c17_Om104 c17_Om112 c17_Om96 R17_1 R17_2 R17_3 R17_4 R17_8 R17_9 R17_10 R17_11 R17_18 R17_19 R17_20 DEF17 HH17 HQ17 ES17 K17 DEFref_17 DEFA_17 DEFd2_17 DEFd3_17 DEFd4_17.
    eapply (seg11 fx17 R0 R R18 M M18 model model18 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A ref u3_20 u3_19 HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 Wu3_20 Wu3_19 R18_2 R18_3 R18_4 R18_8 R18_9 R18_18 R18_19 R18_20 c18_Sm536 c18_Sm544 c18_Sm552 c18_Sm560 c18_Sm568 c18_Sm576 c18_Sm584 c18_Sm592 c18_Sm600 c18_Sm608 c18_Sm616 c18_Sm624 c18_Sm632 c18_Sm488 c18_Sm496 c18_Sm424 c18_Sm432 c18_Sm440 c18_Sm72 c18_Sm80 c18_Sm88 c18_Sm96 c18_Sm104 c18_Sm112 c18_Sm120 c18_Sm128 c18_Sm136 c18_Sm144 c18_Sm152 c18_Sm160 c18_Sm168 c18_Sm24 c18_Sm32 c18_Sm8 c18_Sm16 c18_Sm808w1 c18_Sm744w1 c18_Sm720 c18_Sm728 c18_Sm712w1 c18_Sm688 c18_Sm696 c18_Sm664w1 c18_Sm528w1 c18_Sm472w1 c18_Sm344w1 c18_Sm280w1 c18_Sm248w1 c18_Sm224 c18_Sm232 c18_Sm200w1 c18_Sm176 c18_Sm184 c18_Sm64w1 c18_Om128z8 c18_Om80z12 c18_Op0 c18_Op8 c18_Fp24 c18_Fp32 c18_Fp40 c18_Fp48 c18_Fp56 c18_Fp64w1 c18_Fp65w1 c18_Fp16w4 c18_Fp8 c18_Fp0 c18_Om8 c18_Om40 c18_Om48 c18_Om56 c18_Om64 c18_Om68w4 c18_Om16 c18_Om120 c18_Om24 c18_Om32 c18_Om88 c18_Om104 c18_Om112 c18_Om96 ES18 DEF18 DEFref_18 DEFA_18 DEFd3_18 DEFd4_18 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH18 MOK18 MBV18 HQ18 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3US10.
