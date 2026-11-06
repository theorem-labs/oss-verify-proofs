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
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3AU L5E3T0U L5E3T1U L5E3PU L5E3R1U L5E3R2U L5E3US5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3US4.
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
Let seg5 := L5E3US5.seg5 L HI LY LYX HIok.

Lemma seg4 (fx6 : FPState) (R0 R R6 : bvmap 5 word) (M M6 : word -> option byte) (model model5 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A msg u3_20 u3_19 u3_18 : Z) :
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
  0 <= u3_18 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R6 (reg 1) = Z_to_bv 64 137512 ->
  (* [comment removed for export] *) getr R6 (reg 2) = Z_to_bv 64 (S - 1024) ->
  (* [comment removed for export] *) getr R6 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R6 (reg 4) = Z_to_bv 64 462648 ->
  (* [comment removed for export] *) getr R6 (reg 8) = Z_to_bv 64 (A + 128) ->
  (* [comment removed for export] *) getr R6 (reg 9) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R6 (reg 10) = Z_to_bv 64 (A + 128) ->
  (* [comment removed for export] *) getr R6 (reg 11) = Z_to_bv 64 (S - 1000) ->
  (* [comment removed for export] *) getr R6 (reg 18) = Z_to_bv 64 u3_18 ->
  (* [comment removed for export] *) getr R6 (reg 19) = Z_to_bv 64 u3_19 ->
  (* [comment removed for export] *) getr R6 (reg 20) = Z_to_bv 64 u3_20 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 952) 136456 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 960) w960 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 968) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 976) w976 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 888) 141312 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 896) (S - 528) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 904) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 912) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 536) 144836 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 544) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 560) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 576) w576 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 584) w584 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 592) w592 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 600) w600 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 608) w608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 616) w616 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 624) w624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 632) w632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 488) 143756 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 424) 141856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 440) (S - 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 72) 140436 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 80) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 88) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 96) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 104) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 112) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 120) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 128) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 136) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 144) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 152) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 160) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 168) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 24) 134416 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 32) (S + 96) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 8) 133204 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 808) fb808 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 744) fb744 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 720) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 728) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 712) fb712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 688) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 696) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 528) fb528 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 472) fb472 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 344) fb344 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 224) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 232) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 200) fb200 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 176) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 184) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (S - 64) fb64 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M6 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M6 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1072) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1064) 137160 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1056) u3_20 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1048) u3_19 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1040) u3_18 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1032) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1024) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1016) 137512 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (msg + 41) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 msg 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (msg + 8) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (msg + 16) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (msg + 24) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (msg + 32) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M6 (msg + 40) 48 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 984) msg ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 992) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M6 (S - 1000) 49 ->
  (* [comment removed for export] *) e1_statics M6 gd fl av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M6 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M6 msg 48 ->
  (* [comment removed for export] *) L5.defined M6 A 144 ->
  (* [comment removed for export] *) L5.defined M6 d1 64 ->
  (* [comment removed for export] *) L5.defined M6 d2 64 ->
  (* [comment removed for export] *) L5.defined M6 d3 64 ->
  (* [comment removed for export] *) L5.defined M6 d4 64 ->
  (* [comment removed for export] *) block_range L msg 48 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d1 64 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (msg + 48 <= A \/ A + 144 <= msg) ->
  (* [comment removed for export] *) (msg + 48 <= d1 \/ d1 + 64 <= msg) ->
  (* [comment removed for export] *) (msg + 48 <= d2 \/ d2 + 64 <= msg) ->
  (* [comment removed for export] *) (msg + 48 <= d3 \/ d3 + 64 <= msg) ->
  (* [comment removed for export] *) (msg + 48 <= d4 \/ d4 + 64 <= msg) ->
  (* [comment removed for export] *) (A + 144 <= d1 \/ d1 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d2 \/ d2 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d3 \/ d3 + 64 <= A) ->
  (* [comment removed for export] *) (A + 144 <= d4 \/ d4 + 64 <= A) ->
  (* [comment removed for export] *) (d1 + 64 <= d2 \/ d2 + 64 <= d1) ->
  (* [comment removed for export] *) (d1 + 64 <= d3 \/ d3 + 64 <= d1) ->
  (* [comment removed for export] *) (d1 + 64 <= d4 \/ d4 + 64 <= d1) ->
  (* [comment removed for export] *) (d2 + 64 <= d3 \/ d3 + 64 <= d2) ->
  (* [comment removed for export] *) (d2 + 64 <= d4 \/ d4 + 64 <= d2) ->
  (* [comment removed for export] *) (d3 + 64 <= d4 \/ d4 + 64 <= d3) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 msg 48 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (cr) 144) 48) M6 (m_vmmaps model5) ->
  (* [comment removed for export] *) model_ok model5 ->
  (* [comment removed for export] *) model_but_vm model model5 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M6 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5USU.e3_landed L (L5USU.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133556 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx6 R6 137268 M6 model5) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 Wu3_20 Wu3_19 Wu3_18 R6_1 R6_2 R6_3 R6_4 R6_8 R6_9 R6_10 R6_11 R6_18 R6_19 R6_20 c6_Sm952 c6_Sm960 c6_Sm968 c6_Sm976 c6_Sm888 c6_Sm896 c6_Sm904 c6_Sm912 c6_Sm536 c6_Sm544 c6_Sm552 c6_Sm560 c6_Sm568 c6_Sm576 c6_Sm584 c6_Sm592 c6_Sm600 c6_Sm608 c6_Sm616 c6_Sm624 c6_Sm632 c6_Sm488 c6_Sm496 c6_Sm424 c6_Sm432 c6_Sm440 c6_Sm72 c6_Sm80 c6_Sm88 c6_Sm96 c6_Sm104 c6_Sm112 c6_Sm120 c6_Sm128 c6_Sm136 c6_Sm144 c6_Sm152 c6_Sm160 c6_Sm168 c6_Sm24 c6_Sm32 c6_Sm8 c6_Sm16 c6_Sm808w1 c6_Sm744w1 c6_Sm720 c6_Sm728 c6_Sm712w1 c6_Sm688 c6_Sm696 c6_Sm664w1 c6_Sm528w1 c6_Sm472w1 c6_Sm344w1 c6_Sm280w1 c6_Sm248w1 c6_Sm224 c6_Sm232 c6_Sm200w1 c6_Sm176 c6_Sm184 c6_Sm64w1 c6_Om128z8 c6_Om80z12 c6_Sm1072 c6_Sm1064 c6_Sm1056 c6_Sm1048 c6_Sm1040 c6_Sm1032 c6_Sm1024 c6_Sm1016 c6_Gp41w1 c6_Gp0 c6_Gp8 c6_Gp16 c6_Gp24 c6_Gp32 c6_Gp40w1 c6_Sm984 c6_Sm992 c6_Sm1000 ES6 DEF6 DEFmsg_6 DEFA_6 DEFd1_6 DEFd2_6 DEFd3_6 DEFd4_6 BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_msg FRSH_A HH6 MOK5 MBV5 HQ6 KE.
  pose proof MOK5 as (Mh & Ml & Mm).
  pose proof BR_msg as (B0_msg & B1_msg & B2_msg & B3_msg & B4_msg). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_msg. unfold hl_ceil in B4_msg.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 1008) mod 16 = 0). { clear - A16. replace (S - 1008) with (S + (-63) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES6 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9.
  pose proof (auxv_cells M6 av uid rnd hw S_13) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  assert (WUW: L5.writable RSEGS M6 462433 6). { apply (writable_img M6 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; kl. }
  assert (WUC: L5.writable RSEGS M6 459776 4). { apply (writable_img M6 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; kl. }
  unshelve epose proof (e3c1u_conc fx6 R6 M6 (S - 1008) (A + 128) msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx7 & R7 & M7 & MS7 & K7 & R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_18 & C7_0 & C7_1 & C7_2 & C7_3 & C7_4 & C7_5 & C7_6 & C7_7 & FR7 & GR7).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF6); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF6); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_6); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_6); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFmsg_6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFmsg_6); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFmsg_6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. apply (L5.defined_sub _ _ _ _ _ DEFmsg_6); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((S - 1000) + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 49 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (S - 1000) 49 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI | kl | kl | first [exact c6_Sm1000 | cellfix c6_Sm1000]] end. }
  { (* [comment removed for export] *) first [exact c6_Sm984 | cellfix c6_Sm984]. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 1) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 1)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 1); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 2) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 2)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 2); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 3) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 3)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 3); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 4) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 4)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 4); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 5) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 5)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 5); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 6) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 6)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 6); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with (msg + Z.of_nat 7) by (cbn; ring); replace b0 with (L5B.byte_k 8028075845441778529 (Z.of_nat 7)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm msg 8028075845441778529 7); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp0 | cellfix c6_Gp0]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 1) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 1)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 1); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 2) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 2)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 2); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 3) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 3)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 3); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 4) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 4)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 4); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 5) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 5)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 5); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 6) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 6)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 6); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 8) + Z.of_nat 7) by (cbn; ring); replace b0 with (L5B.byte_k 7863351059373564014 (Z.of_nat 7)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 8) 7863351059373564014 7); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp8 | cellfix c6_Gp8]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 1) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 1)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 1); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 2) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 2)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 2); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 3) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 3)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 3); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 4) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 4)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 4); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 5) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 5)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 5); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 6) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 6)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 6); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 16) + Z.of_nat 7) by (cbn; ring); replace b0 with (L5B.byte_k 2838809733452757089 (Z.of_nat 7)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 16) 2838809733452757089 7); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp16 | cellfix c6_Gp16]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 1) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 1)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 1); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 2) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 2)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 2); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 3) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 3)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 3); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 4) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 4)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 4); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 5) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 5)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 5); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 6) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 6)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 6); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 24) + Z.of_nat 7) by (cbn; ring); replace b0 with (L5B.byte_k 2334102023183623712 (Z.of_nat 7)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 24) 2334102023183623712 7); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp24 | cellfix c6_Gp24]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 0) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 0)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 0); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 1) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 1)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 1); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 2) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 2)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 2); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 3) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 3)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 3); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 4) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 4)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 4); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 5) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 5)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 5); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 6) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 6)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 6); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) lazymatch goal with |- L5.u8_at _ ?mm ?a0 ?b0 => replace a0 with ((msg + 32) + Z.of_nat 7) by (cbn; ring); replace b0 with (L5B.byte_k 4188416081412519009 (Z.of_nat 7)) by reflexivity; apply (L5B.u8_of_u64 RSEGS mm (msg + 32) 4188416081412519009 7); [kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg | kl | kl | first [exact c6_Gp32 | cellfix c6_Gp32]] end. }
  { (* [comment removed for export] *) first [exact c6_Gp40w1 | cellfix c6_Gp40w1]. }
  { (* [comment removed for export] *) first [exact c6_Gp41w1 | cellfix c6_Gp41w1]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS7.
  (* [comment removed for export] *)
  assert (AG7: forall a k, ((a + k <= (S - 1152) \/ (S - 1024) <= a) /\ (a + k <= (A + 128) \/ (A + 136) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M6 M7 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & E1 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR7; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E1 Hi; lia]. }
  assert (R7_1n: getr R7 (reg 1) = Z_to_bv 64 371656) by (rewrite R7_1; f_equal; ring). clear R7_1. rename R7_1n into R7_1.
  assert (R7_2n: getr R7 (reg 2) = Z_to_bv 64 (S - 1088)) by (rewrite R7_2; f_equal; ring). clear R7_2. rename R7_2n into R7_2.
  assert (R7_3: getr R7 (reg 3) = Z_to_bv 64 67584) by (kin K7 3%nat; exact R6_3).
  assert (R7_4: getr R7 (reg 4) = Z_to_bv 64 462648) by (kin K7 4%nat; exact R6_4).
  assert (R7_8n: getr R7 (reg 8) = Z_to_bv 64 66) by (rewrite R7_8; f_equal; ring). clear R7_8. rename R7_8n into R7_8.
  assert (R7_9n: getr R7 (reg 9) = Z_to_bv 64 msg) by (rewrite R7_9; f_equal; ring). clear R7_9. rename R7_9n into R7_9.
  assert (R7_10n: getr R7 (reg 10) = Z_to_bv 64 66) by (rewrite R7_10; f_equal; ring). clear R7_10. rename R7_10n into R7_10.
  assert (R7_18n: getr R7 (reg 18) = Z_to_bv 64 41) by (rewrite R7_18; f_equal; ring). clear R7_18. rename R7_18n into R7_18.
  assert (R7_19: getr R7 (reg 19) = Z_to_bv 64 u3_19) by (kin K7 19%nat; exact R6_19).
  assert (R7_20: getr R7 (reg 20) = Z_to_bv 64 u3_20) by (kin K7 20%nat; exact R6_20).
  assert (c7_Sm952: L5.u64_at RSEGS M7 (S - 952) 136456) by (clear - AG7 c6_Sm952 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm952]).
  assert (c7_Sm960: L5.u64_at RSEGS M7 (S - 960) w960) by (clear - AG7 c6_Sm960 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm960]).
  assert (c7_Sm968: L5.u64_at RSEGS M7 (S - 968) (S + 64)) by (clear - AG7 c6_Sm968 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm968]).
  assert (c7_Sm976: L5.u64_at RSEGS M7 (S - 976) w976) by (clear - AG7 c6_Sm976 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm976]).
  assert (c7_Sm888: L5.u64_at RSEGS M7 (S - 888) 141312) by (clear - AG7 c6_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm888]).
  assert (c7_Sm896: L5.u64_at RSEGS M7 (S - 896) (S - 528)) by (clear - AG7 c6_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm896]).
  assert (c7_Sm904: L5.u64_at RSEGS M7 (S - 904) (S + 64)) by (clear - AG7 c6_Sm904 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm904]).
  assert (c7_Sm912: L5.u64_at RSEGS M7 (S - 912) (S + 64)) by (clear - AG7 c6_Sm912 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm912]).
  assert (c7_Sm536: L5.u64_at RSEGS M7 (S - 536) 144836) by (clear - AG7 c6_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm536]).
  assert (c7_Sm544: L5.u64_at RSEGS M7 (S - 544) (S + 64)) by (clear - AG7 c6_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm544]).
  assert (c7_Sm552: L5.u64_at RSEGS M7 (S - 552) w552) by (clear - AG7 c6_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm552]).
  assert (c7_Sm560: L5.u64_at RSEGS M7 (S - 560) (S + 64)) by (clear - AG7 c6_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm560]).
  assert (c7_Sm568: L5.u64_at RSEGS M7 (S - 568) w568) by (clear - AG7 c6_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm568]).
  assert (c7_Sm576: L5.u64_at RSEGS M7 (S - 576) w576) by (clear - AG7 c6_Sm576 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm576]).
  assert (c7_Sm584: L5.u64_at RSEGS M7 (S - 584) w584) by (clear - AG7 c6_Sm584 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm584]).
  assert (c7_Sm592: L5.u64_at RSEGS M7 (S - 592) w592) by (clear - AG7 c6_Sm592 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm592]).
  assert (c7_Sm600: L5.u64_at RSEGS M7 (S - 600) w600) by (clear - AG7 c6_Sm600 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm600]).
  assert (c7_Sm608: L5.u64_at RSEGS M7 (S - 608) w608) by (clear - AG7 c6_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm608]).
  assert (c7_Sm616: L5.u64_at RSEGS M7 (S - 616) w616) by (clear - AG7 c6_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm616]).
  assert (c7_Sm624: L5.u64_at RSEGS M7 (S - 624) w624) by (clear - AG7 c6_Sm624 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm624]).
  assert (c7_Sm632: L5.u64_at RSEGS M7 (S - 632) w632) by (clear - AG7 c6_Sm632 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm632]).
  assert (c7_Sm488: L5.u64_at RSEGS M7 (S - 488) 143756) by (clear - AG7 c6_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm488]).
  assert (c7_Sm496: L5.u64_at RSEGS M7 (S - 496) (S + 64)) by (clear - AG7 c6_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm496]).
  assert (c7_Sm424: L5.u64_at RSEGS M7 (S - 424) 141856) by (clear - AG7 c6_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm424]).
  assert (c7_Sm432: L5.u64_at RSEGS M7 (S - 432) (S + 64)) by (clear - AG7 c6_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm432]).
  assert (c7_Sm440: L5.u64_at RSEGS M7 (S - 440) (S - 64)) by (clear - AG7 c6_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm440]).
  assert (c7_Sm72: L5.u64_at RSEGS M7 (S - 72) 140436) by (clear - AG7 c6_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm72]).
  assert (c7_Sm80: L5.u64_at RSEGS M7 (S - 80) (S + 64)) by (clear - AG7 c6_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm80]).
  assert (c7_Sm88: L5.u64_at RSEGS M7 (S - 88) (U R0 9)) by (clear - AG7 c6_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm88]).
  assert (c7_Sm96: L5.u64_at RSEGS M7 (S - 96) (U R0 18)) by (clear - AG7 c6_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm96]).
  assert (c7_Sm104: L5.u64_at RSEGS M7 (S - 104) (U R0 19)) by (clear - AG7 c6_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm104]).
  assert (c7_Sm112: L5.u64_at RSEGS M7 (S - 112) (U R0 20)) by (clear - AG7 c6_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm112]).
  assert (c7_Sm120: L5.u64_at RSEGS M7 (S - 120) (U R0 21)) by (clear - AG7 c6_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm120]).
  assert (c7_Sm128: L5.u64_at RSEGS M7 (S - 128) (U R0 22)) by (clear - AG7 c6_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm128]).
  assert (c7_Sm136: L5.u64_at RSEGS M7 (S - 136) (U R0 23)) by (clear - AG7 c6_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm136]).
  assert (c7_Sm144: L5.u64_at RSEGS M7 (S - 144) (U R0 24)) by (clear - AG7 c6_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm144]).
  assert (c7_Sm152: L5.u64_at RSEGS M7 (S - 152) (U R0 25)) by (clear - AG7 c6_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm152]).
  assert (c7_Sm160: L5.u64_at RSEGS M7 (S - 160) (U R0 26)) by (clear - AG7 c6_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm160]).
  assert (c7_Sm168: L5.u64_at RSEGS M7 (S - 168) (U R0 27)) by (clear - AG7 c6_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm168]).
  assert (c7_Sm24: L5.u64_at RSEGS M7 (S - 24) 134416) by (clear - AG7 c6_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm24]).
  assert (c7_Sm32: L5.u64_at RSEGS M7 (S - 32) (S + 96)) by (clear - AG7 c6_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm32]).
  assert (c7_Sm8: L5.u64_at RSEGS M7 (S - 8) 133204) by (clear - AG7 c6_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm8]).
  assert (c7_Sm16: L5.u64_at RSEGS M7 (S - 16) (U R0 8)) by (clear - AG7 c6_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm16]).
  assert (c7_Sm808w1: L5.u8_at RSEGS M7 (S - 808) fb808) by (clear - AG7 c6_Sm808w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm808w1]).
  assert (c7_Sm744w1: L5.u8_at RSEGS M7 (S - 744) fb744) by (clear - AG7 c6_Sm744w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm744w1]).
  assert (c7_Sm720: L5.u64_at RSEGS M7 (S - 720) d1) by (clear - AG7 c6_Sm720 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm720]).
  assert (c7_Sm728: L5.u64_at RSEGS M7 (S - 728) 8) by (clear - AG7 c6_Sm728 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm728]).
  assert (c7_Sm712w1: L5.u8_at RSEGS M7 (S - 712) fb712) by (clear - AG7 c6_Sm712w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm712w1]).
  assert (c7_Sm688: L5.u64_at RSEGS M7 (S - 688) d2) by (clear - AG7 c6_Sm688 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm688]).
  assert (c7_Sm696: L5.u64_at RSEGS M7 (S - 696) 8) by (clear - AG7 c6_Sm696 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm696]).
  assert (c7_Sm664w1: L5.u8_at RSEGS M7 (S - 664) fb664) by (clear - AG7 c6_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm664w1]).
  assert (c7_Sm528w1: L5.u8_at RSEGS M7 (S - 528) fb528) by (clear - AG7 c6_Sm528w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm528w1]).
  assert (c7_Sm472w1: L5.u8_at RSEGS M7 (S - 472) fb472) by (clear - AG7 c6_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm472w1]).
  assert (c7_Sm344w1: L5.u8_at RSEGS M7 (S - 344) fb344) by (clear - AG7 c6_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm344w1]).
  assert (c7_Sm280w1: L5.u8_at RSEGS M7 (S - 280) fb280) by (clear - AG7 c6_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm280w1]).
  assert (c7_Sm248w1: L5.u8_at RSEGS M7 (S - 248) fb248) by (clear - AG7 c6_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm248w1]).
  assert (c7_Sm224: L5.u64_at RSEGS M7 (S - 224) d3) by (clear - AG7 c6_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm224]).
  assert (c7_Sm232: L5.u64_at RSEGS M7 (S - 232) 8) by (clear - AG7 c6_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm232]).
  assert (c7_Sm200w1: L5.u8_at RSEGS M7 (S - 200) fb200) by (clear - AG7 c6_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm200w1]).
  assert (c7_Sm176: L5.u64_at RSEGS M7 (S - 176) d4) by (clear - AG7 c6_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm176]).
  assert (c7_Sm184: L5.u64_at RSEGS M7 (S - 184) 8) by (clear - AG7 c6_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm184]).
  assert (c7_Sm64w1: L5.u8_at RSEGS M7 (S - 64) fb64) by (clear - AG7 c6_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Sm64w1]).
  assert (c7_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M7 (A + i) 0)) by (clear - AG7 c6_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | apply c6_Om128z8; exact Hi]).
  assert (c7_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M7 ((A + 48) + i) 0)) by (clear - AG7 c6_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | apply c6_Om80z12; exact Hi]).
  assert (c7_Sm1024: L5.u64_at RSEGS M7 (S - 1024) (A + 128)) by (clear - AG7 c6_Sm1024 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm1024]).
  assert (c7_Sm1016: L5.u64_at RSEGS M7 (S - 1016) 137512) by (clear - AG7 c6_Sm1016 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm1016]).
  assert (c7_Gp41w1: L5.u8_at RSEGS M7 (msg + 41) 0) by (clear - AG7 c6_Gp41w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Gp41w1]).
  assert (c7_Gp0: L5.u64_at RSEGS M7 msg 8028075845441778529) by (clear - AG7 c6_Gp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Gp0]).
  assert (c7_Gp8: L5.u64_at RSEGS M7 (msg + 8) 7863351059373564014) by (clear - AG7 c6_Gp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Gp8]).
  assert (c7_Gp16: L5.u64_at RSEGS M7 (msg + 16) 2838809733452757089) by (clear - AG7 c6_Gp16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Gp16]).
  assert (c7_Gp24: L5.u64_at RSEGS M7 (msg + 24) 2334102023183623712) by (clear - AG7 c6_Gp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Gp24]).
  assert (c7_Gp32: L5.u64_at RSEGS M7 (msg + 32) 4188416081412519009) by (clear - AG7 c6_Gp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Gp32]).
  assert (c7_Gp40w1: L5.u8_at RSEGS M7 (msg + 40) 48) by (clear - AG7 c6_Gp40w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg B0_A B1_A B3_A B4_A AP_msg_A; eapply (tr8 M6 M7 _ _ _ (AG7 _ 1)); [lia | exact c6_Gp40w1]).
  assert (c7_Sm984: L5.u64_at RSEGS M7 (S - 984) msg) by (clear - AG7 c6_Sm984 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm984]).
  assert (c7_Sm992: L5.u64_at RSEGS M7 (S - 992) 41) by (clear - AG7 c6_Sm992 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm992]).
  assert (c7_Sm1000: L5.u64_at RSEGS M7 (S - 1000) 49) by (clear - AG7 c6_Sm1000 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M6 M7 _ _ _ (AG7 _ 8)); [lia | exact c6_Sm1000]).
  assert (c7_Sm1088: L5.u64_at RSEGS M7 (S - 1088) (A + 128)) by (cellfix C7_0). clear C7_0.
  assert (c7_Sm1080: L5.u64_at RSEGS M7 (S - 1080) 266272) by (cellfix C7_1). clear C7_1.
  assert (c7_Op0: L5.u64_at RSEGS M7 (A + 128) 387952) by (cellfix C7_2). clear C7_2.
  rewrite R6_19, BG.unsigned_lit in C7_3 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_19).
  assert (c7_Sm1064: L5.u64_at RSEGS M7 (S - 1064) u3_19) by (cellfix C7_3). clear C7_3.
  rewrite R6_18, BG.unsigned_lit in C7_4 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_18).
  assert (c7_Sm1056: L5.u64_at RSEGS M7 (S - 1056) u3_18) by (cellfix C7_4). clear C7_4.
  rewrite R6_9, BG.unsigned_lit in C7_5 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI).
  assert (c7_Sm1048: L5.u64_at RSEGS M7 (S - 1048) (S + 64)) by (cellfix C7_5). clear C7_5.
  rewrite R6_8, BG.unsigned_lit in C7_6 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A).
  assert (c7_Sm1040: L5.u64_at RSEGS M7 (S - 1040) (A + 128)) by (cellfix C7_6). clear C7_6.
  assert (c7_Sm1032: L5.u64_at RSEGS M7 (S - 1032) 137272) by (cellfix C7_7). clear C7_7.
  assert (STAT7: forall a, stat_rd av a -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { clear - FR7 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR7; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (e1_statics_keep M6 M7 gd fl av uid rnd canary hw ES6 STAT7) as ES7.
  assert (DEF7: L5.defined M7 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR7 | exact DEF6]).
  assert (DEFmsg_7: L5.defined M7 msg 48) by (eapply L5.defined_grows; [exact GR7 | exact DEFmsg_6]).
  assert (DEFA_7: L5.defined M7 A 144) by (eapply L5.defined_grows; [exact GR7 | exact DEFA_6]).
  assert (DEFd1_7: L5.defined M7 d1 64) by (eapply L5.defined_grows; [exact GR7 | exact DEFd1_6]).
  assert (DEFd2_7: L5.defined M7 d2 64) by (eapply L5.defined_grows; [exact GR7 | exact DEFd2_6]).
  assert (DEFd3_7: L5.defined M7 d3 64) by (eapply L5.defined_grows; [exact GR7 | exact DEFd3_6]).
  assert (DEFd4_7: L5.defined M7 d4 64) by (eapply L5.defined_grows; [exact GR7 | exact DEFd4_6]).
  assert (HH7: hi_heap HI ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (cr) 144) 48) M7 (m_vmmaps model5)).
  { clear - HH6 GR7 FR7 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply hi_heap_clientx. exact HH6. lia. 2: exact GR7. intros a Ha.
    destruct (in_dec (S - 1152) (S - 1024) a) as [IN0|OUT0]. { right; left; lia. }
    destruct (in_dec (A + 128) (A + 136) a) as [IN1|OUT1]. { right; right; left; exists (A, 144); split; [right; left; reflexivity| cbn; lia]. }
    left; apply FR7; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ7: L5C.hpres L LB1 S 10240 XSF M M7).
  { clear - LBWF HQ6 FR7 GR7 IMGHI STOP ERR LY FRSH_A LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M6 M7 [((S - 1152), 128); ((A + 128), 8)]). exact LBWF. lia. exact HQ6.
    { intros x Hx. apply FR7; intros Hin.
      - apply (Hx ((S - 1152), 128)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((A + 128), 8)). right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR7.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. eapply L5PK.wr_fresh. exact FRSH_A. lia. lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG7 FR7 MS7. try clear STAT7. try clear K6.
  try clear c6_Sm952. try clear c6_Sm960. try clear c6_Sm968. try clear c6_Sm976. try clear c6_Sm888. try clear c6_Sm896. try clear c6_Sm904. try clear c6_Sm912. try clear c6_Sm536. try clear c6_Sm544. try clear c6_Sm552. try clear c6_Sm560. try clear c6_Sm568. try clear c6_Sm576. try clear c6_Sm584. try clear c6_Sm592. try clear c6_Sm600. try clear c6_Sm608. try clear c6_Sm616. try clear c6_Sm624. try clear c6_Sm632. try clear c6_Sm488. try clear c6_Sm496. try clear c6_Sm424. try clear c6_Sm432. try clear c6_Sm440. try clear c6_Sm72. try clear c6_Sm80. try clear c6_Sm88. try clear c6_Sm96. try clear c6_Sm104. try clear c6_Sm112. try clear c6_Sm120. try clear c6_Sm128. try clear c6_Sm136. try clear c6_Sm144. try clear c6_Sm152. try clear c6_Sm160. try clear c6_Sm168. try clear c6_Sm24. try clear c6_Sm32. try clear c6_Sm8. try clear c6_Sm16. try clear c6_Sm808w1. try clear c6_Sm744w1. try clear c6_Sm720. try clear c6_Sm728. try clear c6_Sm712w1. try clear c6_Sm688. try clear c6_Sm696. try clear c6_Sm664w1. try clear c6_Sm528w1. try clear c6_Sm472w1. try clear c6_Sm344w1. try clear c6_Sm280w1. try clear c6_Sm248w1. try clear c6_Sm224. try clear c6_Sm232. try clear c6_Sm200w1. try clear c6_Sm176. try clear c6_Sm184. try clear c6_Sm64w1. try clear c6_Om128z8. try clear c6_Om80z12. try clear c6_Sm1072. try clear c6_Sm1064. try clear c6_Sm1056. try clear c6_Sm1048. try clear c6_Sm1040. try clear c6_Sm1032. try clear c6_Sm1024. try clear c6_Sm1016. try clear c6_Gp41w1. try clear c6_Gp0. try clear c6_Gp8. try clear c6_Gp16. try clear c6_Gp24. try clear c6_Gp32. try clear c6_Gp40w1. try clear c6_Sm984. try clear c6_Sm992. try clear c6_Sm1000. try clear R6_1. try clear R6_2. try clear R6_3. try clear R6_4. try clear R6_8. try clear R6_9. try clear R6_10. try clear R6_11. try clear R6_18. try clear R6_19. try clear R6_20. try clear DEF6. try clear HH6. try clear HQ6. try clear ES6. try clear DEFmsg_6. try clear DEFA_6. try clear DEFd1_6. try clear DEFd2_6. try clear DEFd3_6. try clear DEFd4_6.
  (* [comment removed for export] *)
  pose proof (hio_malloc L SCFG HI HIok fx7 R7 M7 model5 ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (cr) 144) 48) 66 K) as HC.
  rewrite (ly_segs L LY), (ly_malloc L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH7.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - rewrite L5CoreKit.L5K.rl10. exact R7_10.
  - kl.
  - exact CR66.
  - rewrite L5CoreKit.L5K.rl4. exact R7_4.
  - rewrite L5CoreKit.L5K.rl1, R7_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R7_2 A16 DEF7 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R7_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-68) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M7 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF7. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R8 M8 model8 ref HA10 RP8 BRn BAn DEFn PRES8 MBVn HH8.
    rewrite L5CoreKit.L5K.rl1, R7_1.
    rewrite L5CoreKit.L5K.rl2, R7_2, BG.unsigned_lit in PRES8 by (kl SLO SHI STOP).
    match type of PRES8 with heap_pres_core _ _ ?x _ _ => replace x with (S - 1088) in PRES8 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 1088) M7 M8 PRES8) as HP8. rewrite (ly_stack L LY) in HP8. unfold HEAP_STACK in HP8.
    assert (AGS8: forall a k, ((S - 1088) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M7 M8 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP8 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP8. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_msg: L5C.agree_on M7 M8 msg 48).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_msg. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_A: L5C.agree_on M7 M8 A 144).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_d1: L5C.agree_on M7 M8 d1 64).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d1. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_d2: L5C.agree_on M7 M8 d2 64).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d2. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_d3: L5C.agree_on M7 M8 d3 64).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB8_d4: L5C.agree_on M7 M8 d4 64).
    { clear - HP8 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP8. right; right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT8: forall a, stat_rd av a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
    { clear - HP8 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 1088) 8224 [] M7 M8 HP8). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (e1_statics_keep M7 M8 gd fl av uid rnd canary hw ES7 STAT8) as ES8.
    assert (DEF8: L5.defined M8 (S - 10240) 10240).
    { clear - HP8 DEF7 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 1088) 8224 [] M7 M8). exact HP8. lia. lia. lia. lia. exact DEF7. }
    assert (DEFmsg_8: L5.defined M8 msg 48) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_msg | exact DEFmsg_7]).
    assert (DEFA_8: L5.defined M8 A 144) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_A | exact DEFA_7]).
    assert (DEFd1_8: L5.defined M8 d1 64) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_d1 | exact DEFd1_7]).
    assert (DEFd2_8: L5.defined M8 d2 64) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_d2 | exact DEFd2_7]).
    assert (DEFd3_8: L5.defined M8 d3 64) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_d3 | exact DEFd3_7]).
    assert (DEFd4_8: L5.defined M8 d4 64) by (eapply (L5C.defined_agree M7 M8); [exact AGB8_d4 | exact DEFd4_7]).
    assert (DEFref_8: L5.defined M8 ref 66) by exact DEFn. clear DEFn.
    pose proof BRn as BR_ref. clear BRn. pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
    pose proof (BAn (msg, 48) ltac:(left; reflexivity)) as AP_ref_msg. cbn [fst snd] in AP_ref_msg.
    pose proof (BAn (A, 144) ltac:(right; left; reflexivity)) as AP_ref_A. cbn [fst snd] in AP_ref_A.
    pose proof (BAn (d1, 64) ltac:(right; right; left; reflexivity)) as AP_ref_d1. cbn [fst snd] in AP_ref_d1.
    pose proof (BAn (d2, 64) ltac:(right; right; right; left; reflexivity)) as AP_ref_d2. cbn [fst snd] in AP_ref_d2.
    pose proof (BAn (d3, 64) ltac:(right; right; right; right; left; reflexivity)) as AP_ref_d3. cbn [fst snd] in AP_ref_d3.
    pose proof (BAn (d4, 64) ltac:(right; right; right; right; right; left; reflexivity)) as AP_ref_d4. cbn [fst snd] in AP_ref_d4.
    assert (FRSH_ref: L5PK.fresh_rng L LB1 ref 66). { clear - BAn LY B0_ref B1_ref B3_ref B4_ref STOP. split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. split. lia. intros bb Hbb. apply BAn. right. right. right. right. right. right.  exact Hbb. }
    clear BAn.
    assert (MOK8: model_ok model8).
    { destruct MOK5 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK8 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV5 MBVn) as MBV8. clear MBVn MBV5.
    assert (RPi8: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R8 (reg i) = getr R7 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R7 R8 i RP8). exact Hi. }
    assert (R8_2: getr R8 (reg 2) = Z_to_bv 64 (S - 1088)) by (rewrite (RPi8 2%nat) by inl; exact R7_2).
    assert (R8_3: getr R8 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi8 3%nat) by inl; exact R7_3).
    assert (R8_4: getr R8 (reg 4) = Z_to_bv 64 462648) by (rewrite (RPi8 4%nat) by inl; exact R7_4).
    assert (R8_8: getr R8 (reg 8) = Z_to_bv 64 66) by (rewrite (RPi8 8%nat) by inl; exact R7_8).
    assert (R8_9: getr R8 (reg 9) = Z_to_bv 64 msg) by (rewrite (RPi8 9%nat) by inl; exact R7_9).
    assert (R8_18: getr R8 (reg 18) = Z_to_bv 64 41) by (rewrite (RPi8 18%nat) by inl; exact R7_18).
    assert (R8_19: getr R8 (reg 19) = Z_to_bv 64 u3_19) by (rewrite (RPi8 19%nat) by inl; exact R7_19).
    assert (R8_20: getr R8 (reg 20) = Z_to_bv 64 u3_20) by (rewrite (RPi8 20%nat) by inl; exact R7_20).
    rewrite L5CoreKit.L5K.rl10 in HA10. rename HA10 into R8_10.
    assert (c8_Sm952: L5.u64_at RSEGS M8 (S - 952) 136456) by (clear - AGS8 c7_Sm952 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm952]).
    assert (c8_Sm960: L5.u64_at RSEGS M8 (S - 960) w960) by (clear - AGS8 c7_Sm960 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm960]).
    assert (c8_Sm968: L5.u64_at RSEGS M8 (S - 968) (S + 64)) by (clear - AGS8 c7_Sm968 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm968]).
    assert (c8_Sm976: L5.u64_at RSEGS M8 (S - 976) w976) by (clear - AGS8 c7_Sm976 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm976]).
    assert (c8_Sm888: L5.u64_at RSEGS M8 (S - 888) 141312) by (clear - AGS8 c7_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm888]).
    assert (c8_Sm896: L5.u64_at RSEGS M8 (S - 896) (S - 528)) by (clear - AGS8 c7_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm896]).
    assert (c8_Sm904: L5.u64_at RSEGS M8 (S - 904) (S + 64)) by (clear - AGS8 c7_Sm904 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm904]).
    assert (c8_Sm912: L5.u64_at RSEGS M8 (S - 912) (S + 64)) by (clear - AGS8 c7_Sm912 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm912]).
    assert (c8_Sm536: L5.u64_at RSEGS M8 (S - 536) 144836) by (clear - AGS8 c7_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm536]).
    assert (c8_Sm544: L5.u64_at RSEGS M8 (S - 544) (S + 64)) by (clear - AGS8 c7_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm544]).
    assert (c8_Sm552: L5.u64_at RSEGS M8 (S - 552) w552) by (clear - AGS8 c7_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm552]).
    assert (c8_Sm560: L5.u64_at RSEGS M8 (S - 560) (S + 64)) by (clear - AGS8 c7_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm560]).
    assert (c8_Sm568: L5.u64_at RSEGS M8 (S - 568) w568) by (clear - AGS8 c7_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm568]).
    assert (c8_Sm576: L5.u64_at RSEGS M8 (S - 576) w576) by (clear - AGS8 c7_Sm576 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm576]).
    assert (c8_Sm584: L5.u64_at RSEGS M8 (S - 584) w584) by (clear - AGS8 c7_Sm584 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm584]).
    assert (c8_Sm592: L5.u64_at RSEGS M8 (S - 592) w592) by (clear - AGS8 c7_Sm592 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm592]).
    assert (c8_Sm600: L5.u64_at RSEGS M8 (S - 600) w600) by (clear - AGS8 c7_Sm600 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm600]).
    assert (c8_Sm608: L5.u64_at RSEGS M8 (S - 608) w608) by (clear - AGS8 c7_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm608]).
    assert (c8_Sm616: L5.u64_at RSEGS M8 (S - 616) w616) by (clear - AGS8 c7_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm616]).
    assert (c8_Sm624: L5.u64_at RSEGS M8 (S - 624) w624) by (clear - AGS8 c7_Sm624 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm624]).
    assert (c8_Sm632: L5.u64_at RSEGS M8 (S - 632) w632) by (clear - AGS8 c7_Sm632 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm632]).
    assert (c8_Sm488: L5.u64_at RSEGS M8 (S - 488) 143756) by (clear - AGS8 c7_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm488]).
    assert (c8_Sm496: L5.u64_at RSEGS M8 (S - 496) (S + 64)) by (clear - AGS8 c7_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm496]).
    assert (c8_Sm424: L5.u64_at RSEGS M8 (S - 424) 141856) by (clear - AGS8 c7_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm424]).
    assert (c8_Sm432: L5.u64_at RSEGS M8 (S - 432) (S + 64)) by (clear - AGS8 c7_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm432]).
    assert (c8_Sm440: L5.u64_at RSEGS M8 (S - 440) (S - 64)) by (clear - AGS8 c7_Sm440 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm440]).
    assert (c8_Sm72: L5.u64_at RSEGS M8 (S - 72) 140436) by (clear - AGS8 c7_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm72]).
    assert (c8_Sm80: L5.u64_at RSEGS M8 (S - 80) (S + 64)) by (clear - AGS8 c7_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm80]).
    assert (c8_Sm88: L5.u64_at RSEGS M8 (S - 88) (U R0 9)) by (clear - AGS8 c7_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm88]).
    assert (c8_Sm96: L5.u64_at RSEGS M8 (S - 96) (U R0 18)) by (clear - AGS8 c7_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm96]).
    assert (c8_Sm104: L5.u64_at RSEGS M8 (S - 104) (U R0 19)) by (clear - AGS8 c7_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm104]).
    assert (c8_Sm112: L5.u64_at RSEGS M8 (S - 112) (U R0 20)) by (clear - AGS8 c7_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm112]).
    assert (c8_Sm120: L5.u64_at RSEGS M8 (S - 120) (U R0 21)) by (clear - AGS8 c7_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm120]).
    assert (c8_Sm128: L5.u64_at RSEGS M8 (S - 128) (U R0 22)) by (clear - AGS8 c7_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm128]).
    assert (c8_Sm136: L5.u64_at RSEGS M8 (S - 136) (U R0 23)) by (clear - AGS8 c7_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm136]).
    assert (c8_Sm144: L5.u64_at RSEGS M8 (S - 144) (U R0 24)) by (clear - AGS8 c7_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm144]).
    assert (c8_Sm152: L5.u64_at RSEGS M8 (S - 152) (U R0 25)) by (clear - AGS8 c7_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm152]).
    assert (c8_Sm160: L5.u64_at RSEGS M8 (S - 160) (U R0 26)) by (clear - AGS8 c7_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm160]).
    assert (c8_Sm168: L5.u64_at RSEGS M8 (S - 168) (U R0 27)) by (clear - AGS8 c7_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm168]).
    assert (c8_Sm24: L5.u64_at RSEGS M8 (S - 24) 134416) by (clear - AGS8 c7_Sm24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm24]).
    assert (c8_Sm32: L5.u64_at RSEGS M8 (S - 32) (S + 96)) by (clear - AGS8 c7_Sm32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm32]).
    assert (c8_Sm8: L5.u64_at RSEGS M8 (S - 8) 133204) by (clear - AGS8 c7_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm8]).
    assert (c8_Sm16: L5.u64_at RSEGS M8 (S - 16) (U R0 8)) by (clear - AGS8 c7_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm16]).
    assert (c8_Sm808w1: L5.u8_at RSEGS M8 (S - 808) fb808) by (clear - AGS8 c7_Sm808w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm808w1]).
    assert (c8_Sm744w1: L5.u8_at RSEGS M8 (S - 744) fb744) by (clear - AGS8 c7_Sm744w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm744w1]).
    assert (c8_Sm720: L5.u64_at RSEGS M8 (S - 720) d1) by (clear - AGS8 c7_Sm720 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm720]).
    assert (c8_Sm728: L5.u64_at RSEGS M8 (S - 728) 8) by (clear - AGS8 c7_Sm728 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm728]).
    assert (c8_Sm712w1: L5.u8_at RSEGS M8 (S - 712) fb712) by (clear - AGS8 c7_Sm712w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm712w1]).
    assert (c8_Sm688: L5.u64_at RSEGS M8 (S - 688) d2) by (clear - AGS8 c7_Sm688 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm688]).
    assert (c8_Sm696: L5.u64_at RSEGS M8 (S - 696) 8) by (clear - AGS8 c7_Sm696 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm696]).
    assert (c8_Sm664w1: L5.u8_at RSEGS M8 (S - 664) fb664) by (clear - AGS8 c7_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm664w1]).
    assert (c8_Sm528w1: L5.u8_at RSEGS M8 (S - 528) fb528) by (clear - AGS8 c7_Sm528w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm528w1]).
    assert (c8_Sm472w1: L5.u8_at RSEGS M8 (S - 472) fb472) by (clear - AGS8 c7_Sm472w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm472w1]).
    assert (c8_Sm344w1: L5.u8_at RSEGS M8 (S - 344) fb344) by (clear - AGS8 c7_Sm344w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm344w1]).
    assert (c8_Sm280w1: L5.u8_at RSEGS M8 (S - 280) fb280) by (clear - AGS8 c7_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm280w1]).
    assert (c8_Sm248w1: L5.u8_at RSEGS M8 (S - 248) fb248) by (clear - AGS8 c7_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm248w1]).
    assert (c8_Sm224: L5.u64_at RSEGS M8 (S - 224) d3) by (clear - AGS8 c7_Sm224 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm224]).
    assert (c8_Sm232: L5.u64_at RSEGS M8 (S - 232) 8) by (clear - AGS8 c7_Sm232 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm232]).
    assert (c8_Sm200w1: L5.u8_at RSEGS M8 (S - 200) fb200) by (clear - AGS8 c7_Sm200w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm200w1]).
    assert (c8_Sm176: L5.u64_at RSEGS M8 (S - 176) d4) by (clear - AGS8 c7_Sm176 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm176]).
    assert (c8_Sm184: L5.u64_at RSEGS M8 (S - 184) 8) by (clear - AGS8 c7_Sm184 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm184]).
    assert (c8_Sm64w1: L5.u8_at RSEGS M8 (S - 64) fb64) by (clear - AGS8 c7_Sm64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M7 M8 _ _ _ (AGS8 _ 1)); [lia | exact c7_Sm64w1]).
    assert (c8_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M8 (A + i) 0)) by (clear - AGB8_A c7_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB8_A); [lia | apply c7_Om128z8; exact Hi]).
    assert (c8_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M8 ((A + 48) + i) 0)) by (clear - AGB8_A c7_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB8_A); [lia | apply c7_Om80z12; exact Hi]).
    assert (c8_Sm1024: L5.u64_at RSEGS M8 (S - 1024) (A + 128)) by (clear - AGS8 c7_Sm1024 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1024]).
    assert (c8_Sm1016: L5.u64_at RSEGS M8 (S - 1016) 137512) by (clear - AGS8 c7_Sm1016 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1016]).
    assert (c8_Gp41w1: L5.u8_at RSEGS M8 (msg + 41) 0) by (clear - AGB8_msg c7_Gp41w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb8 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp41w1]).
    assert (c8_Gp0: L5.u64_at RSEGS M8 msg 8028075845441778529) by (clear - AGB8_msg c7_Gp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb64 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp0]).
    assert (c8_Gp8: L5.u64_at RSEGS M8 (msg + 8) 7863351059373564014) by (clear - AGB8_msg c7_Gp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb64 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp8]).
    assert (c8_Gp16: L5.u64_at RSEGS M8 (msg + 16) 2838809733452757089) by (clear - AGB8_msg c7_Gp16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb64 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp16]).
    assert (c8_Gp24: L5.u64_at RSEGS M8 (msg + 24) 2334102023183623712) by (clear - AGB8_msg c7_Gp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb64 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp24]).
    assert (c8_Gp32: L5.u64_at RSEGS M8 (msg + 32) 4188416081412519009) by (clear - AGB8_msg c7_Gp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb64 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp32]).
    assert (c8_Gp40w1: L5.u8_at RSEGS M8 (msg + 40) 48) by (clear - AGB8_msg c7_Gp40w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (trb8 _ _ _ _ _ _ AGB8_msg); [lia | exact c7_Gp40w1]).
    assert (c8_Sm984: L5.u64_at RSEGS M8 (S - 984) msg) by (clear - AGS8 c7_Sm984 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm984]).
    assert (c8_Sm992: L5.u64_at RSEGS M8 (S - 992) 41) by (clear - AGS8 c7_Sm992 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm992]).
    assert (c8_Sm1000: L5.u64_at RSEGS M8 (S - 1000) 49) by (clear - AGS8 c7_Sm1000 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1000]).
    assert (c8_Sm1088: L5.u64_at RSEGS M8 (S - 1088) (A + 128)) by (clear - AGS8 c7_Sm1088 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1088]).
    assert (c8_Sm1080: L5.u64_at RSEGS M8 (S - 1080) 266272) by (clear - AGS8 c7_Sm1080 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1080]).
    assert (c8_Op0: L5.u64_at RSEGS M8 (A + 128) 387952) by (clear - AGB8_A c7_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB8_A); [lia | exact c7_Op0]).
    assert (c8_Sm1064: L5.u64_at RSEGS M8 (S - 1064) u3_19) by (clear - AGS8 c7_Sm1064 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1064]).
    assert (c8_Sm1056: L5.u64_at RSEGS M8 (S - 1056) u3_18) by (clear - AGS8 c7_Sm1056 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1056]).
    assert (c8_Sm1048: L5.u64_at RSEGS M8 (S - 1048) (S + 64)) by (clear - AGS8 c7_Sm1048 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1048]).
    assert (c8_Sm1040: L5.u64_at RSEGS M8 (S - 1040) (A + 128)) by (clear - AGS8 c7_Sm1040 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1040]).
    assert (c8_Sm1032: L5.u64_at RSEGS M8 (S - 1032) 137272) by (clear - AGS8 c7_Sm1032 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M7 M8 _ _ _ (AGS8 _ 8)); [lia | exact c7_Sm1032]).
    assert (HQ8: L5C.hpres L LB1 S 10240 XSF M M8).
    { clear - LBWF HQ7 HP8 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 1088) 8224 [] M M7 M8). exact LBWF. lia. lia. exact HQ7. exact HP8. intros bb Hbb; right; right; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS8 STAT8 PRES8 RP8 RPi8 HP8 AGB8_msg AGB8_A AGB8_d1 AGB8_d2 AGB8_d3 AGB8_d4.
    try clear c7_Sm952 c7_Sm960 c7_Sm968 c7_Sm976 c7_Sm888 c7_Sm896 c7_Sm904 c7_Sm912 c7_Sm536 c7_Sm544 c7_Sm552 c7_Sm560 c7_Sm568 c7_Sm576 c7_Sm584 c7_Sm592 c7_Sm600 c7_Sm608 c7_Sm616 c7_Sm624 c7_Sm632 c7_Sm488 c7_Sm496 c7_Sm424 c7_Sm432 c7_Sm440 c7_Sm72 c7_Sm80 c7_Sm88 c7_Sm96 c7_Sm104 c7_Sm112 c7_Sm120 c7_Sm128 c7_Sm136 c7_Sm144 c7_Sm152 c7_Sm160 c7_Sm168 c7_Sm24 c7_Sm32 c7_Sm8 c7_Sm16 c7_Sm808w1 c7_Sm744w1 c7_Sm720 c7_Sm728 c7_Sm712w1 c7_Sm688 c7_Sm696 c7_Sm664w1 c7_Sm528w1 c7_Sm472w1 c7_Sm344w1 c7_Sm280w1 c7_Sm248w1 c7_Sm224 c7_Sm232 c7_Sm200w1 c7_Sm176 c7_Sm184 c7_Sm64w1 c7_Om128z8 c7_Om80z12 c7_Sm1024 c7_Sm1016 c7_Gp41w1 c7_Gp0 c7_Gp8 c7_Gp16 c7_Gp24 c7_Gp32 c7_Gp40w1 c7_Sm984 c7_Sm992 c7_Sm1000 c7_Sm1088 c7_Sm1080 c7_Op0 c7_Sm1064 c7_Sm1056 c7_Sm1048 c7_Sm1040 c7_Sm1032 R7_1 R7_2 R7_3 R7_4 R7_8 R7_9 R7_10 R7_18 R7_19 R7_20 DEF7 HH7 HQ7 ES7 K7 DEFmsg_7 DEFA_7 DEFd1_7 DEFd2_7 DEFd3_7 DEFd4_7.
    eapply (seg5 fx7 R0 R R8 M M8 model model8 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 A msg ref u3_20 u3_19 u3_18 HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 Ww960 Ww976 Ww552 Ww568 Ww576 Ww584 Ww592 Ww600 Ww608 Ww616 Ww624 Ww632 Wu3_20 Wu3_19 Wu3_18 R8_2 R8_3 R8_4 R8_8 R8_9 R8_10 R8_18 R8_19 R8_20 c8_Sm952 c8_Sm960 c8_Sm968 c8_Sm976 c8_Sm888 c8_Sm896 c8_Sm904 c8_Sm912 c8_Sm536 c8_Sm544 c8_Sm552 c8_Sm560 c8_Sm568 c8_Sm576 c8_Sm584 c8_Sm592 c8_Sm600 c8_Sm608 c8_Sm616 c8_Sm624 c8_Sm632 c8_Sm488 c8_Sm496 c8_Sm424 c8_Sm432 c8_Sm440 c8_Sm72 c8_Sm80 c8_Sm88 c8_Sm96 c8_Sm104 c8_Sm112 c8_Sm120 c8_Sm128 c8_Sm136 c8_Sm144 c8_Sm152 c8_Sm160 c8_Sm168 c8_Sm24 c8_Sm32 c8_Sm8 c8_Sm16 c8_Sm808w1 c8_Sm744w1 c8_Sm720 c8_Sm728 c8_Sm712w1 c8_Sm688 c8_Sm696 c8_Sm664w1 c8_Sm528w1 c8_Sm472w1 c8_Sm344w1 c8_Sm280w1 c8_Sm248w1 c8_Sm224 c8_Sm232 c8_Sm200w1 c8_Sm176 c8_Sm184 c8_Sm64w1 c8_Om128z8 c8_Om80z12 c8_Sm1024 c8_Sm1016 c8_Gp41w1 c8_Gp0 c8_Gp8 c8_Gp16 c8_Gp24 c8_Gp32 c8_Gp40w1 c8_Sm984 c8_Sm992 c8_Sm1000 c8_Sm1088 c8_Sm1080 c8_Op0 c8_Sm1064 c8_Sm1056 c8_Sm1048 c8_Sm1040 c8_Sm1032 ES8 DEF8 DEFref_8 DEFmsg_8 DEFA_8 DEFd1_8 DEFd2_8 DEFd3_8 DEFd4_8 BR_ref BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_msg AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_msg FRSH_A HH8 MOK8 MBV8 HQ8 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3US4.
