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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore BigLinkBase BigLinkGlue BigModel
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S13.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S12.
Import L5CS L5PS L5STRK L5E2K L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)).

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
Proof. intros AG HP H. destruct (AG HP) as (G & Ha & Hn). exact (L5US.u32_at_agree Mo Mn a v G Ha Hn H). Qed.
Lemma tr8 Mo Mn a v (P : Prop) : (P -> L5C.agree_on Mo Mn a 1 /\ 0 <= a /\ a + 1 <= 2 ^ 64) -> P -> L5.u8_at RSEGS Mo a v -> L5.u8_at RSEGS Mn a v.
Proof. intros AG HP H. destruct (AG HP) as (G & Ha & Hn). exact (L5C.u8_at_agree RSEGS Mo Mn a v G Ha Hn H). Qed.
Lemma trb64 Mo Mn b n a v : L5C.agree_on Mo Mn b n -> (b <= a /\ a + 8 <= b + n /\ 0 <= a /\ a + 8 <= 2 ^ 64) -> L5.u64_at RSEGS Mo a v -> L5.u64_at RSEGS Mn a v.
Proof. intros AG (H1 & H2 & Ha & Hn) H. exact (L5C.u64_at_agree RSEGS Mo Mn a v (L5C.agree_on_sub Mo Mn b n a 8 AG H1 H2) Ha Hn H). Qed.
Lemma trb32 Mo Mn b n a v : L5C.agree_on Mo Mn b n -> (b <= a /\ a + 4 <= b + n /\ 0 <= a /\ a + 4 <= 2 ^ 64) -> L5.u32_at RSEGS Mo a v -> L5.u32_at RSEGS Mn a v.
Proof. intros AG (H1 & H2 & Ha & Hn) H. exact (L5US.u32_at_agree Mo Mn a v (L5C.agree_on_sub Mo Mn b n a 4 AG H1 H2) Ha Hn H). Qed.
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
Let XSF : list L5.range := [(456960, 4); (459617, 6)].
Let seg13 := L5E3S13.seg13 L HI LY LYX HIok.

Lemma seg12 (fx20 : FPState) (R0 R R20 : bvmap 5 word) (M M20 : word -> option byte) (model model18 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref : Z) :
  K [] ->
  getr R0 (reg 2) = Z_to_bv 64 S -> getr R0 (reg 3) = Z_to_bv 64 67584 -> getr R0 (reg 4) = Z_to_bv 64 459832 ->
  S mod 16 = 0 -> hl_sptop L - 2 ^ 23 + 10240 <= S -> S + 240 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  hl_sptop L <= av -> L5PK.lb_wf L LB1 ->
  credit_ok L cr 144 -> credit_ok L (debit L cr 144) 48 -> credit_ok L (debit L (debit L cr 144) 48) 66 ->
  0 <= fb696 < 256 -> Z.testbit fb696 0 = false ->
  0 <= fb664 < 256 -> Z.testbit fb664 0 = true ->
  0 <= fb632 < 256 -> Z.testbit fb632 0 = true ->
  0 <= fb600 < 256 -> Z.testbit fb600 0 = false ->
  0 <= fb464 < 256 -> Z.testbit fb464 0 = false ->
  0 <= fb408 < 256 -> Z.testbit fb408 0 = false ->
  0 <= fb280 < 256 -> Z.testbit fb280 0 = false ->
  0 <= fb248 < 256 -> Z.testbit fb248 0 = false ->
  0 <= fb216 < 256 -> Z.testbit fb216 0 = true ->
  0 <= fb184 < 256 -> Z.testbit fb184 0 = true ->
  0 <= fb48 < 256 -> Z.testbit fb48 0 = false ->
  0 <= w856 < 2 ^ 64 ->
  0 <= w864 < 2 ^ 64 ->
  0 <= w872 < 2 ^ 64 ->
  0 <= w784 < 2 ^ 64 ->
  0 <= w488 < 2 ^ 64 ->
  0 <= w504 < 2 ^ 64 ->
  0 <= w512 < 2 ^ 64 ->
  0 <= w520 < 2 ^ 64 ->
  0 <= w528 < 2 ^ 64 ->
  0 <= w536 < 2 ^ 64 ->
  0 <= w544 < 2 ^ 64 ->
  0 <= w552 < 2 ^ 64 ->
  0 <= w560 < 2 ^ 64 ->
  0 <= w568 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R20 (reg 1) = Z_to_bv 64 142188 ->
  (* [comment removed for export] *) getr R20 (reg 2) = Z_to_bv 64 (S - 464) ->
  (* [comment removed for export] *) getr R20 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R20 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R20 (reg 8) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R20 (reg 9) = Z_to_bv 64 w488 ->
  (* [comment removed for export] *) getr R20 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R20 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R20 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R20 (reg 19) = Z_to_bv 64 w504 ->
  (* [comment removed for export] *) getr R20 (reg 20) = Z_to_bv 64 w512 ->
  (* [comment removed for export] *) getr R20 (reg 21) = Z_to_bv 64 w520 ->
  (* [comment removed for export] *) getr R20 (reg 22) = Z_to_bv 64 w528 ->
  (* [comment removed for export] *) getr R20 (reg 23) = Z_to_bv 64 w536 ->
  (* [comment removed for export] *) getr R20 (reg 24) = Z_to_bv 64 w544 ->
  (* [comment removed for export] *) getr R20 (reg 25) = Z_to_bv 64 w552 ->
  (* [comment removed for export] *) getr R20 (reg 26) = Z_to_bv 64 w560 ->
  (* [comment removed for export] *) getr R20 (reg 27) = Z_to_bv 64 w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M20 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M20 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M20 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M20 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M20 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M20 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M20 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M20 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M20 ref 66 ->
  (* [comment removed for export] *) L5.defined M20 A 144 ->
  (* [comment removed for export] *) L5.defined M20 d3 64 ->
  (* [comment removed for export] *) L5.defined M20 d4 64 ->
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
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M20 (m_vmmaps model18) ->
  (* [comment removed for export] *) model_ok model18 ->
  (* [comment removed for export] *) model_but_vm model model18 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M20 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx20 R20 142188 M20 model18) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R20_1 R20_2 R20_3 R20_4 R20_8 R20_9 R20_10 R20_11 R20_18 R20_19 R20_20 R20_21 R20_22 R20_23 R20_24 R20_25 R20_26 R20_27 c20_Sm472 c20_Sm480 c20_Sm488 c20_Sm496 c20_Sm504 c20_Sm512 c20_Sm520 c20_Sm528 c20_Sm536 c20_Sm544 c20_Sm552 c20_Sm560 c20_Sm568 c20_Sm424 c20_Sm432 c20_Sm360 c20_Sm368 c20_Sm376 c20_Sm56 c20_Sm64 c20_Sm72 c20_Sm80 c20_Sm88 c20_Sm96 c20_Sm104 c20_Sm112 c20_Sm120 c20_Sm128 c20_Sm136 c20_Sm144 c20_Sm152 c20_Sm8 c20_Sm16 c20_Sm696w1 c20_Sm664w1 c20_Sm640 c20_Sm648 c20_Sm632w1 c20_Sm608 c20_Sm616 c20_Sm600w1 c20_Sm464w1 c20_Sm408w1 c20_Sm280w1 c20_Sm248w1 c20_Sm216w1 c20_Sm192 c20_Sm200 c20_Sm184w1 c20_Sm160 c20_Sm168 c20_Sm48w1 c20_Om128z8 c20_Om80z12 c20_Op0 c20_Op8 c20_Fp24 c20_Fp32 c20_Fp40 c20_Fp48 c20_Fp56 c20_Fp64w1 c20_Fp65w1 c20_Fp16w4 c20_Fp8 c20_Fp0 c20_Om8 c20_Om40 c20_Om48 c20_Om56 c20_Om64 c20_Om68w4 c20_Om16 c20_Om120 c20_Om24 c20_Om32 c20_Om88 c20_Om104 c20_Om112 c20_Om96 ES20 DEF20 DEFref_20 DEFA_20 DEFd3_20 DEFd4_20 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH20 MOK18 MBV18 HQ20 KE.
  pose proof MOK18 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES20 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES20 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M20 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p3_conc fx20 R20 M20 (S - 896) (A + 128) fb464 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx21 & R21 & M21 & MS21 & K21 & R21_2 & R21_8 & R21_10 & R21_11 & FR21 & GR21).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb464. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF20 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF20); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF20 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF20); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_20 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_20); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_20 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_20); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb464. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c20_Sm464w1 | cellfix c20_Sm464w1]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS21.
  (* [comment removed for export] *)
  assert (AG21: forall a k, ((a + k <= (S - 528) \/ (S - 464) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M20 M21 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR21; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R21_1: getr R21 (reg 1) = Z_to_bv 64 142188) by (kin K21 1%nat; exact R20_1).
  assert (R21_2n: getr R21 (reg 2) = Z_to_bv 64 (S - 464)) by (rewrite R21_2; f_equal; ring). clear R21_2. rename R21_2n into R21_2.
  assert (R21_3: getr R21 (reg 3) = Z_to_bv 64 67584) by (kin K21 3%nat; exact R20_3).
  assert (R21_4: getr R21 (reg 4) = Z_to_bv 64 459832) by (kin K21 4%nat; exact R20_4).
  assert (R21_8n: getr R21 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R21_8; f_equal; ring). clear R21_8. rename R21_8n into R21_8.
  assert (R21_9: getr R21 (reg 9) = Z_to_bv 64 w488) by (kin K21 9%nat; exact R20_9).
  assert (R21_10n: getr R21 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R21_10; f_equal; ring). clear R21_10. rename R21_10n into R21_10.
  assert (R21_11n: getr R21 (reg 11) = Z_to_bv 64 0) by (rewrite R21_11; f_equal; ring). clear R21_11. rename R21_11n into R21_11.
  assert (R21_18: getr R21 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K21 18%nat; exact R20_18).
  assert (R21_19: getr R21 (reg 19) = Z_to_bv 64 w504) by (kin K21 19%nat; exact R20_19).
  assert (R21_20: getr R21 (reg 20) = Z_to_bv 64 w512) by (kin K21 20%nat; exact R20_20).
  assert (R21_21: getr R21 (reg 21) = Z_to_bv 64 w520) by (kin K21 21%nat; exact R20_21).
  assert (R21_22: getr R21 (reg 22) = Z_to_bv 64 w528) by (kin K21 22%nat; exact R20_22).
  assert (R21_23: getr R21 (reg 23) = Z_to_bv 64 w536) by (kin K21 23%nat; exact R20_23).
  assert (R21_24: getr R21 (reg 24) = Z_to_bv 64 w544) by (kin K21 24%nat; exact R20_24).
  assert (R21_25: getr R21 (reg 25) = Z_to_bv 64 w552) by (kin K21 25%nat; exact R20_25).
  assert (R21_26: getr R21 (reg 26) = Z_to_bv 64 w560) by (kin K21 26%nat; exact R20_26).
  assert (R21_27: getr R21 (reg 27) = Z_to_bv 64 w568) by (kin K21 27%nat; exact R20_27).
  assert (c21_Sm536: L5.u64_at RSEGS M21 (S - 536) w536) by (clear - AG21 c20_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm536]).
  assert (c21_Sm544: L5.u64_at RSEGS M21 (S - 544) w544) by (clear - AG21 c20_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm544]).
  assert (c21_Sm552: L5.u64_at RSEGS M21 (S - 552) w552) by (clear - AG21 c20_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm552]).
  assert (c21_Sm560: L5.u64_at RSEGS M21 (S - 560) w560) by (clear - AG21 c20_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm560]).
  assert (c21_Sm568: L5.u64_at RSEGS M21 (S - 568) w568) by (clear - AG21 c20_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm568]).
  assert (c21_Sm424: L5.u64_at RSEGS M21 (S - 424) 141264) by (clear - AG21 c20_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm424]).
  assert (c21_Sm432: L5.u64_at RSEGS M21 (S - 432) (S + 64)) by (clear - AG21 c20_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm432]).
  assert (c21_Sm360: L5.u64_at RSEGS M21 (S - 360) 139904) by (clear - AG21 c20_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm360]).
  assert (c21_Sm368: L5.u64_at RSEGS M21 (S - 368) (S + 64)) by (clear - AG21 c20_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm368]).
  assert (c21_Sm376: L5.u64_at RSEGS M21 (S - 376) (S - 48)) by (clear - AG21 c20_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm376]).
  assert (c21_Sm56: L5.u64_at RSEGS M21 (S - 56) 138528) by (clear - AG21 c20_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm56]).
  assert (c21_Sm64: L5.u64_at RSEGS M21 (S - 64) (S + 64)) by (clear - AG21 c20_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm64]).
  assert (c21_Sm72: L5.u64_at RSEGS M21 (S - 72) (U R0 9)) by (clear - AG21 c20_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm72]).
  assert (c21_Sm80: L5.u64_at RSEGS M21 (S - 80) (U R0 18)) by (clear - AG21 c20_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm80]).
  assert (c21_Sm88: L5.u64_at RSEGS M21 (S - 88) (U R0 19)) by (clear - AG21 c20_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm88]).
  assert (c21_Sm96: L5.u64_at RSEGS M21 (S - 96) (U R0 20)) by (clear - AG21 c20_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm96]).
  assert (c21_Sm104: L5.u64_at RSEGS M21 (S - 104) (U R0 21)) by (clear - AG21 c20_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm104]).
  assert (c21_Sm112: L5.u64_at RSEGS M21 (S - 112) (U R0 22)) by (clear - AG21 c20_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm112]).
  assert (c21_Sm120: L5.u64_at RSEGS M21 (S - 120) (U R0 23)) by (clear - AG21 c20_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm120]).
  assert (c21_Sm128: L5.u64_at RSEGS M21 (S - 128) (U R0 24)) by (clear - AG21 c20_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm128]).
  assert (c21_Sm136: L5.u64_at RSEGS M21 (S - 136) (U R0 25)) by (clear - AG21 c20_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm136]).
  assert (c21_Sm144: L5.u64_at RSEGS M21 (S - 144) (U R0 26)) by (clear - AG21 c20_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm144]).
  assert (c21_Sm152: L5.u64_at RSEGS M21 (S - 152) (U R0 27)) by (clear - AG21 c20_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm152]).
  assert (c21_Sm8: L5.u64_at RSEGS M21 (S - 8) 132608) by (clear - AG21 c20_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm8]).
  assert (c21_Sm16: L5.u64_at RSEGS M21 (S - 16) (U R0 8)) by (clear - AG21 c20_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm16]).
  assert (c21_Sm696w1: L5.u8_at RSEGS M21 (S - 696) fb696) by (clear - AG21 c20_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm696w1]).
  assert (c21_Sm664w1: L5.u8_at RSEGS M21 (S - 664) fb664) by (clear - AG21 c20_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm664w1]).
  assert (c21_Sm640: L5.u64_at RSEGS M21 (S - 640) d1) by (clear - AG21 c20_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm640]).
  assert (c21_Sm648: L5.u64_at RSEGS M21 (S - 648) 8) by (clear - AG21 c20_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm648]).
  assert (c21_Sm632w1: L5.u8_at RSEGS M21 (S - 632) fb632) by (clear - AG21 c20_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm632w1]).
  assert (c21_Sm608: L5.u64_at RSEGS M21 (S - 608) d2) by (clear - AG21 c20_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm608]).
  assert (c21_Sm616: L5.u64_at RSEGS M21 (S - 616) 8) by (clear - AG21 c20_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm616]).
  assert (c21_Sm600w1: L5.u8_at RSEGS M21 (S - 600) fb600) by (clear - AG21 c20_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm600w1]).
  assert (c21_Sm464w1: L5.u8_at RSEGS M21 (S - 464) fb464) by (clear - AG21 c20_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm464w1]).
  assert (c21_Sm408w1: L5.u8_at RSEGS M21 (S - 408) fb408) by (clear - AG21 c20_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm408w1]).
  assert (c21_Sm280w1: L5.u8_at RSEGS M21 (S - 280) fb280) by (clear - AG21 c20_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm280w1]).
  assert (c21_Sm248w1: L5.u8_at RSEGS M21 (S - 248) fb248) by (clear - AG21 c20_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm248w1]).
  assert (c21_Sm216w1: L5.u8_at RSEGS M21 (S - 216) fb216) by (clear - AG21 c20_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm216w1]).
  assert (c21_Sm192: L5.u64_at RSEGS M21 (S - 192) d3) by (clear - AG21 c20_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm192]).
  assert (c21_Sm200: L5.u64_at RSEGS M21 (S - 200) 8) by (clear - AG21 c20_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm200]).
  assert (c21_Sm184w1: L5.u8_at RSEGS M21 (S - 184) fb184) by (clear - AG21 c20_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm184w1]).
  assert (c21_Sm160: L5.u64_at RSEGS M21 (S - 160) d4) by (clear - AG21 c20_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm160]).
  assert (c21_Sm168: L5.u64_at RSEGS M21 (S - 168) 8) by (clear - AG21 c20_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Sm168]).
  assert (c21_Sm48w1: L5.u8_at RSEGS M21 (S - 48) fb48) by (clear - AG21 c20_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Sm48w1]).
  assert (c21_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M21 (A + i) 0)) by (clear - AG21 c20_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | apply c20_Om128z8; exact Hi]).
  assert (c21_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M21 ((A + 48) + i) 0)) by (clear - AG21 c20_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | apply c20_Om80z12; exact Hi]).
  assert (c21_Op0: L5.u64_at RSEGS M21 (A + 128) 373272) by (clear - AG21 c20_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Op0]).
  assert (c21_Op8: L5.u64_at RSEGS M21 (A + 136) (ref + 24)) by (clear - AG21 c20_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Op8]).
  assert (c21_Fp24: L5.u64_at RSEGS M21 (ref + 24) 8028075845441778529) by (clear - AG21 c20_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp24]).
  assert (c21_Fp32: L5.u64_at RSEGS M21 (ref + 32) 7863351059373564014) by (clear - AG21 c20_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp32]).
  assert (c21_Fp40: L5.u64_at RSEGS M21 (ref + 40) 2838809733452757089) by (clear - AG21 c20_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp40]).
  assert (c21_Fp48: L5.u64_at RSEGS M21 (ref + 48) 2334102023183623712) by (clear - AG21 c20_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp48]).
  assert (c21_Fp56: L5.u64_at RSEGS M21 (ref + 56) 4188416081412519009) by (clear - AG21 c20_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp56]).
  assert (c21_Fp64w1: L5.u8_at RSEGS M21 (ref + 64) 48) by (clear - AG21 c20_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Fp64w1]).
  assert (c21_Fp65w1: L5.u8_at RSEGS M21 (ref + 65) 0) by (clear - AG21 c20_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M20 M21 _ _ _ (AG21 _ 1)); [lia | exact c20_Fp65w1]).
  assert (c21_Fp16w4: L5.u32_at RSEGS M21 (ref + 16) 0) by (clear - AG21 c20_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M20 M21 _ _ _ (AG21 _ 4)); [lia | exact c20_Fp16w4]).
  assert (c21_Fp8: L5.u64_at RSEGS M21 (ref + 8) 41) by (clear - AG21 c20_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp8]).
  assert (c21_Fp0: L5.u64_at RSEGS M21 ref 41) by (clear - AG21 c20_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Fp0]).
  assert (c21_Om8: L5.u64_at RSEGS M21 (A + 120) S) by (clear - AG21 c20_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om8]).
  assert (c21_Om40: L5.u64_at RSEGS M21 (A + 88) (A + 128)) by (clear - AG21 c20_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om40]).
  assert (c21_Om48: L5.u64_at RSEGS M21 (A + 80) 133016) by (clear - AG21 c20_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om48]).
  assert (c21_Om56: L5.u64_at RSEGS M21 (A + 72) 91560) by (clear - AG21 c20_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om56]).
  assert (c21_Om64: L5.u64_at RSEGS M21 (A + 64) 91699) by (clear - AG21 c20_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om64]).
  assert (c21_Om68w4: L5.u32_at RSEGS M21 (A + 60) 1) by (clear - AG21 c20_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M20 M21 _ _ _ (AG21 _ 4)); [lia | exact c20_Om68w4]).
  assert (c21_Om16: L5.u64_at RSEGS M21 (A + 112) 0) by (clear - AG21 c20_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om16]).
  assert (c21_Om120: L5.u64_at RSEGS M21 (A + 8) 1) by (clear - AG21 c20_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om120]).
  assert (c21_Om24: L5.u64_at RSEGS M21 (A + 104) 257624) by (clear - AG21 c20_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om24]).
  assert (c21_Om32: L5.u64_at RSEGS M21 (A + 96) 4849336966747728640) by (clear - AG21 c20_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om32]).
  assert (c21_Om88: L5.u64_at RSEGS M21 (A + 40) 142700) by (clear - AG21 c20_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om88]).
  assert (c21_Om104: L5.u64_at RSEGS M21 (A + 24) 253816) by (clear - AG21 c20_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om104]).
  assert (c21_Om112: L5.u64_at RSEGS M21 (A + 16) 373232) by (clear - AG21 c20_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om112]).
  assert (c21_Om96: L5.u64_at RSEGS M21 (A + 32) 142968) by (clear - AG21 c20_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M20 M21 _ _ _ (AG21 _ 8)); [lia | exact c20_Om96]).
  assert (STAT21: forall a, stat_rd av a -> M21 (Z_to_bv 64 a) = M20 (Z_to_bv 64 a)).
  { clear - FR21 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR21; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M20 M21 gd av uid rnd canary hw ES20 STAT21) as ES21.
  assert (DEF21: L5.defined M21 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR21 | exact DEF20]).
  assert (DEFref_21: L5.defined M21 ref 66) by (eapply L5.defined_grows; [exact GR21 | exact DEFref_20]).
  assert (DEFA_21: L5.defined M21 A 144) by (eapply L5.defined_grows; [exact GR21 | exact DEFA_20]).
  assert (DEFd3_21: L5.defined M21 d3 64) by (eapply L5.defined_grows; [exact GR21 | exact DEFd3_20]).
  assert (DEFd4_21: L5.defined M21 d4 64) by (eapply L5.defined_grows; [exact GR21 | exact DEFd4_20]).
  assert (HH21: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M21 (m_vmmaps model18)).
  { clear - HH20 GR21 FR21 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH20. lia. 2: exact GR21. intros a Ha.
    destruct (in_dec (S - 528) (S - 464) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR21; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ21: L5C.hpres L LB1 S 10240 XSF M M21).
  { clear - LBWF HQ20 FR21 GR21 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M20 M21 [((S - 528), 64)]). exact LBWF. lia. exact HQ20.
    { intros x Hx. apply FR21; intros Hin.
        apply (Hx ((S - 528), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR21.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG21 FR21 MS21. try clear STAT21. try clear K20.
  try clear c20_Sm472. try clear c20_Sm480. try clear c20_Sm488. try clear c20_Sm496. try clear c20_Sm504. try clear c20_Sm512. try clear c20_Sm520. try clear c20_Sm528. try clear c20_Sm536. try clear c20_Sm544. try clear c20_Sm552. try clear c20_Sm560. try clear c20_Sm568. try clear c20_Sm424. try clear c20_Sm432. try clear c20_Sm360. try clear c20_Sm368. try clear c20_Sm376. try clear c20_Sm56. try clear c20_Sm64. try clear c20_Sm72. try clear c20_Sm80. try clear c20_Sm88. try clear c20_Sm96. try clear c20_Sm104. try clear c20_Sm112. try clear c20_Sm120. try clear c20_Sm128. try clear c20_Sm136. try clear c20_Sm144. try clear c20_Sm152. try clear c20_Sm8. try clear c20_Sm16. try clear c20_Sm696w1. try clear c20_Sm664w1. try clear c20_Sm640. try clear c20_Sm648. try clear c20_Sm632w1. try clear c20_Sm608. try clear c20_Sm616. try clear c20_Sm600w1. try clear c20_Sm464w1. try clear c20_Sm408w1. try clear c20_Sm280w1. try clear c20_Sm248w1. try clear c20_Sm216w1. try clear c20_Sm192. try clear c20_Sm200. try clear c20_Sm184w1. try clear c20_Sm160. try clear c20_Sm168. try clear c20_Sm48w1. try clear c20_Om128z8. try clear c20_Om80z12. try clear c20_Op0. try clear c20_Op8. try clear c20_Fp24. try clear c20_Fp32. try clear c20_Fp40. try clear c20_Fp48. try clear c20_Fp56. try clear c20_Fp64w1. try clear c20_Fp65w1. try clear c20_Fp16w4. try clear c20_Fp8. try clear c20_Fp0. try clear c20_Om8. try clear c20_Om40. try clear c20_Om48. try clear c20_Om56. try clear c20_Om64. try clear c20_Om68w4. try clear c20_Om16. try clear c20_Om120. try clear c20_Om24. try clear c20_Om32. try clear c20_Om88. try clear c20_Om104. try clear c20_Om112. try clear c20_Om96. try clear R20_1. try clear R20_2. try clear R20_3. try clear R20_4. try clear R20_8. try clear R20_9. try clear R20_10. try clear R20_11. try clear R20_18. try clear R20_19. try clear R20_20. try clear R20_21. try clear R20_22. try clear R20_23. try clear R20_24. try clear R20_25. try clear R20_26. try clear R20_27. try clear DEF20. try clear HH20. try clear HQ20. try clear ES20. try clear DEFref_20. try clear DEFA_20. try clear DEFd3_20. try clear DEFd4_20.
  (* [comment removed for export] *)
  pose proof ES21 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M21 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r3_conc fx21 R21 M21 (S - 896) (A + 128) av canary uid rnd hw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx22 & R22 & M22 & MS22 & K22 & R22_1 & R22_2 & R22_8 & R22_10 & R22_11 & FR22 & GR22).
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
  { (* [comment removed for export] *) clear - DEF21 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF21); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF21 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF21); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_21 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_21); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_21 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_21); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c21_Om16 | cellfix c21_Om16]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c21_Om8 | cellfix c21_Om8]. }
  { (* [comment removed for export] *) first [exact c21_Om32 | cellfix c21_Om32]. }
  { (* [comment removed for export] *) first [exact c21_Sm424 | cellfix c21_Sm424]. }
  { (* [comment removed for export] *) first [exact c21_Sm432 | cellfix c21_Sm432]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS22.
  (* [comment removed for export] *)
  assert (AG22: forall a k, ((a + k <= (S - 8832) \/ (S - 464) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M21 M22 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR22; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R22_1n: getr R22 (reg 1) = Z_to_bv 64 141340) by (rewrite R22_1; f_equal; ring). clear R22_1. rename R22_1n into R22_1.
  assert (R22_2n: getr R22 (reg 2) = Z_to_bv 64 (S - 416)) by (rewrite R22_2; f_equal; ring). clear R22_2. rename R22_2n into R22_2.
  assert (R22_3: getr R22 (reg 3) = Z_to_bv 64 67584) by (kin K22 3%nat; exact R21_3).
  assert (R22_4: getr R22 (reg 4) = Z_to_bv 64 459832) by (kin K22 4%nat; exact R21_4).
  assert (R22_8n: getr R22 (reg 8) = Z_to_bv 64 (S + 64)) by (rewrite R22_8; f_equal; ring). clear R22_8. rename R22_8n into R22_8.
  assert (R22_9: getr R22 (reg 9) = Z_to_bv 64 w488) by (kin K22 9%nat; exact R21_9).
  assert (R22_10n: getr R22 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R22_10; f_equal; ring). clear R22_10. rename R22_10n into R22_10.
  assert (R22_11n: getr R22 (reg 11) = Z_to_bv 64 0) by (rewrite R22_11; f_equal; ring). clear R22_11. rename R22_11n into R22_11.
  assert (R22_18: getr R22 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K22 18%nat; exact R21_18).
  assert (R22_19: getr R22 (reg 19) = Z_to_bv 64 w504) by (kin K22 19%nat; exact R21_19).
  assert (R22_20: getr R22 (reg 20) = Z_to_bv 64 w512) by (kin K22 20%nat; exact R21_20).
  assert (R22_21: getr R22 (reg 21) = Z_to_bv 64 w520) by (kin K22 21%nat; exact R21_21).
  assert (R22_22: getr R22 (reg 22) = Z_to_bv 64 w528) by (kin K22 22%nat; exact R21_22).
  assert (R22_23: getr R22 (reg 23) = Z_to_bv 64 w536) by (kin K22 23%nat; exact R21_23).
  assert (R22_24: getr R22 (reg 24) = Z_to_bv 64 w544) by (kin K22 24%nat; exact R21_24).
  assert (R22_25: getr R22 (reg 25) = Z_to_bv 64 w552) by (kin K22 25%nat; exact R21_25).
  assert (R22_26: getr R22 (reg 26) = Z_to_bv 64 w560) by (kin K22 26%nat; exact R21_26).
  assert (R22_27: getr R22 (reg 27) = Z_to_bv 64 w568) by (kin K22 27%nat; exact R21_27).
  assert (c22_Sm424: L5.u64_at RSEGS M22 (S - 424) 141264) by (clear - AG22 c21_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm424]).
  assert (c22_Sm432: L5.u64_at RSEGS M22 (S - 432) (S + 64)) by (clear - AG22 c21_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm432]).
  assert (c22_Sm360: L5.u64_at RSEGS M22 (S - 360) 139904) by (clear - AG22 c21_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm360]).
  assert (c22_Sm368: L5.u64_at RSEGS M22 (S - 368) (S + 64)) by (clear - AG22 c21_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm368]).
  assert (c22_Sm376: L5.u64_at RSEGS M22 (S - 376) (S - 48)) by (clear - AG22 c21_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm376]).
  assert (c22_Sm56: L5.u64_at RSEGS M22 (S - 56) 138528) by (clear - AG22 c21_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm56]).
  assert (c22_Sm64: L5.u64_at RSEGS M22 (S - 64) (S + 64)) by (clear - AG22 c21_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm64]).
  assert (c22_Sm72: L5.u64_at RSEGS M22 (S - 72) (U R0 9)) by (clear - AG22 c21_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm72]).
  assert (c22_Sm80: L5.u64_at RSEGS M22 (S - 80) (U R0 18)) by (clear - AG22 c21_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm80]).
  assert (c22_Sm88: L5.u64_at RSEGS M22 (S - 88) (U R0 19)) by (clear - AG22 c21_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm88]).
  assert (c22_Sm96: L5.u64_at RSEGS M22 (S - 96) (U R0 20)) by (clear - AG22 c21_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm96]).
  assert (c22_Sm104: L5.u64_at RSEGS M22 (S - 104) (U R0 21)) by (clear - AG22 c21_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm104]).
  assert (c22_Sm112: L5.u64_at RSEGS M22 (S - 112) (U R0 22)) by (clear - AG22 c21_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm112]).
  assert (c22_Sm120: L5.u64_at RSEGS M22 (S - 120) (U R0 23)) by (clear - AG22 c21_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm120]).
  assert (c22_Sm128: L5.u64_at RSEGS M22 (S - 128) (U R0 24)) by (clear - AG22 c21_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm128]).
  assert (c22_Sm136: L5.u64_at RSEGS M22 (S - 136) (U R0 25)) by (clear - AG22 c21_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm136]).
  assert (c22_Sm144: L5.u64_at RSEGS M22 (S - 144) (U R0 26)) by (clear - AG22 c21_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm144]).
  assert (c22_Sm152: L5.u64_at RSEGS M22 (S - 152) (U R0 27)) by (clear - AG22 c21_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm152]).
  assert (c22_Sm8: L5.u64_at RSEGS M22 (S - 8) 132608) by (clear - AG22 c21_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm8]).
  assert (c22_Sm16: L5.u64_at RSEGS M22 (S - 16) (U R0 8)) by (clear - AG22 c21_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm16]).
  assert (c22_Sm464w1: L5.u8_at RSEGS M22 (S - 464) fb464) by (clear - AG22 c21_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm464w1]).
  assert (c22_Sm408w1: L5.u8_at RSEGS M22 (S - 408) fb408) by (clear - AG22 c21_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm408w1]).
  assert (c22_Sm280w1: L5.u8_at RSEGS M22 (S - 280) fb280) by (clear - AG22 c21_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm280w1]).
  assert (c22_Sm248w1: L5.u8_at RSEGS M22 (S - 248) fb248) by (clear - AG22 c21_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm248w1]).
  assert (c22_Sm216w1: L5.u8_at RSEGS M22 (S - 216) fb216) by (clear - AG22 c21_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm216w1]).
  assert (c22_Sm192: L5.u64_at RSEGS M22 (S - 192) d3) by (clear - AG22 c21_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm192]).
  assert (c22_Sm200: L5.u64_at RSEGS M22 (S - 200) 8) by (clear - AG22 c21_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm200]).
  assert (c22_Sm184w1: L5.u8_at RSEGS M22 (S - 184) fb184) by (clear - AG22 c21_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm184w1]).
  assert (c22_Sm160: L5.u64_at RSEGS M22 (S - 160) d4) by (clear - AG22 c21_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm160]).
  assert (c22_Sm168: L5.u64_at RSEGS M22 (S - 168) 8) by (clear - AG22 c21_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Sm168]).
  assert (c22_Sm48w1: L5.u8_at RSEGS M22 (S - 48) fb48) by (clear - AG22 c21_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Sm48w1]).
  assert (c22_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M22 (A + i) 0)) by (clear - AG22 c21_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | apply c21_Om128z8; exact Hi]).
  assert (c22_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M22 ((A + 48) + i) 0)) by (clear - AG22 c21_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | apply c21_Om80z12; exact Hi]).
  assert (c22_Op0: L5.u64_at RSEGS M22 (A + 128) 373272) by (clear - AG22 c21_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Op0]).
  assert (c22_Op8: L5.u64_at RSEGS M22 (A + 136) (ref + 24)) by (clear - AG22 c21_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Op8]).
  assert (c22_Fp24: L5.u64_at RSEGS M22 (ref + 24) 8028075845441778529) by (clear - AG22 c21_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp24]).
  assert (c22_Fp32: L5.u64_at RSEGS M22 (ref + 32) 7863351059373564014) by (clear - AG22 c21_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp32]).
  assert (c22_Fp40: L5.u64_at RSEGS M22 (ref + 40) 2838809733452757089) by (clear - AG22 c21_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp40]).
  assert (c22_Fp48: L5.u64_at RSEGS M22 (ref + 48) 2334102023183623712) by (clear - AG22 c21_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp48]).
  assert (c22_Fp56: L5.u64_at RSEGS M22 (ref + 56) 4188416081412519009) by (clear - AG22 c21_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp56]).
  assert (c22_Fp64w1: L5.u8_at RSEGS M22 (ref + 64) 48) by (clear - AG22 c21_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Fp64w1]).
  assert (c22_Fp65w1: L5.u8_at RSEGS M22 (ref + 65) 0) by (clear - AG22 c21_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M21 M22 _ _ _ (AG22 _ 1)); [lia | exact c21_Fp65w1]).
  assert (c22_Fp16w4: L5.u32_at RSEGS M22 (ref + 16) 0) by (clear - AG22 c21_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M21 M22 _ _ _ (AG22 _ 4)); [lia | exact c21_Fp16w4]).
  assert (c22_Fp8: L5.u64_at RSEGS M22 (ref + 8) 41) by (clear - AG22 c21_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp8]).
  assert (c22_Fp0: L5.u64_at RSEGS M22 ref 41) by (clear - AG22 c21_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Fp0]).
  assert (c22_Om8: L5.u64_at RSEGS M22 (A + 120) S) by (clear - AG22 c21_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om8]).
  assert (c22_Om40: L5.u64_at RSEGS M22 (A + 88) (A + 128)) by (clear - AG22 c21_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om40]).
  assert (c22_Om48: L5.u64_at RSEGS M22 (A + 80) 133016) by (clear - AG22 c21_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om48]).
  assert (c22_Om56: L5.u64_at RSEGS M22 (A + 72) 91560) by (clear - AG22 c21_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om56]).
  assert (c22_Om64: L5.u64_at RSEGS M22 (A + 64) 91699) by (clear - AG22 c21_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om64]).
  assert (c22_Om68w4: L5.u32_at RSEGS M22 (A + 60) 1) by (clear - AG22 c21_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M21 M22 _ _ _ (AG22 _ 4)); [lia | exact c21_Om68w4]).
  assert (c22_Om16: L5.u64_at RSEGS M22 (A + 112) 0) by (clear - AG22 c21_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om16]).
  assert (c22_Om120: L5.u64_at RSEGS M22 (A + 8) 1) by (clear - AG22 c21_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om120]).
  assert (c22_Om24: L5.u64_at RSEGS M22 (A + 104) 257624) by (clear - AG22 c21_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om24]).
  assert (c22_Om32: L5.u64_at RSEGS M22 (A + 96) 4849336966747728640) by (clear - AG22 c21_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om32]).
  assert (c22_Om88: L5.u64_at RSEGS M22 (A + 40) 142700) by (clear - AG22 c21_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om88]).
  assert (c22_Om104: L5.u64_at RSEGS M22 (A + 24) 253816) by (clear - AG22 c21_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om104]).
  assert (c22_Om112: L5.u64_at RSEGS M22 (A + 16) 373232) by (clear - AG22 c21_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om112]).
  assert (c22_Om96: L5.u64_at RSEGS M22 (A + 32) 142968) by (clear - AG22 c21_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M21 M22 _ _ _ (AG22 _ 8)); [lia | exact c21_Om96]).
  assert (STAT22: forall a, stat_rd av a -> M22 (Z_to_bv 64 a) = M21 (Z_to_bv 64 a)).
  { clear - FR22 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR22; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M21 M22 gd av uid rnd canary hw ES21 STAT22) as ES22.
  assert (DEF22: L5.defined M22 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR22 | exact DEF21]).
  assert (DEFref_22: L5.defined M22 ref 66) by (eapply L5.defined_grows; [exact GR22 | exact DEFref_21]).
  assert (DEFA_22: L5.defined M22 A 144) by (eapply L5.defined_grows; [exact GR22 | exact DEFA_21]).
  assert (DEFd3_22: L5.defined M22 d3 64) by (eapply L5.defined_grows; [exact GR22 | exact DEFd3_21]).
  assert (DEFd4_22: L5.defined M22 d4 64) by (eapply L5.defined_grows; [exact GR22 | exact DEFd4_21]).
  assert (HH22: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M22 (m_vmmaps model18)).
  { clear - HH21 GR22 FR22 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH21. lia. 2: exact GR22. intros a Ha.
    destruct (in_dec (S - 8832) (S - 464) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR22; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ22: L5C.hpres L LB1 S 10240 XSF M M22).
  { clear - LBWF HQ21 FR22 GR22 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M21 M22 [((S - 8832), 8368)]). exact LBWF. lia. exact HQ21.
    { intros x Hx. apply FR22; intros Hin.
        apply (Hx ((S - 8832), 8368)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR22.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG22 FR22 MS22. try clear STAT22. try clear K21.
  try clear c21_Sm536. try clear c21_Sm544. try clear c21_Sm552. try clear c21_Sm560. try clear c21_Sm568. try clear c21_Sm424. try clear c21_Sm432. try clear c21_Sm360. try clear c21_Sm368. try clear c21_Sm376. try clear c21_Sm56. try clear c21_Sm64. try clear c21_Sm72. try clear c21_Sm80. try clear c21_Sm88. try clear c21_Sm96. try clear c21_Sm104. try clear c21_Sm112. try clear c21_Sm120. try clear c21_Sm128. try clear c21_Sm136. try clear c21_Sm144. try clear c21_Sm152. try clear c21_Sm8. try clear c21_Sm16. try clear c21_Sm696w1. try clear c21_Sm664w1. try clear c21_Sm640. try clear c21_Sm648. try clear c21_Sm632w1. try clear c21_Sm608. try clear c21_Sm616. try clear c21_Sm600w1. try clear c21_Sm464w1. try clear c21_Sm408w1. try clear c21_Sm280w1. try clear c21_Sm248w1. try clear c21_Sm216w1. try clear c21_Sm192. try clear c21_Sm200. try clear c21_Sm184w1. try clear c21_Sm160. try clear c21_Sm168. try clear c21_Sm48w1. try clear c21_Om128z8. try clear c21_Om80z12. try clear c21_Op0. try clear c21_Op8. try clear c21_Fp24. try clear c21_Fp32. try clear c21_Fp40. try clear c21_Fp48. try clear c21_Fp56. try clear c21_Fp64w1. try clear c21_Fp65w1. try clear c21_Fp16w4. try clear c21_Fp8. try clear c21_Fp0. try clear c21_Om8. try clear c21_Om40. try clear c21_Om48. try clear c21_Om56. try clear c21_Om64. try clear c21_Om68w4. try clear c21_Om16. try clear c21_Om120. try clear c21_Om24. try clear c21_Om32. try clear c21_Om88. try clear c21_Om104. try clear c21_Om112. try clear c21_Om96. try clear R21_1. try clear R21_2. try clear R21_3. try clear R21_4. try clear R21_8. try clear R21_9. try clear R21_10. try clear R21_11. try clear R21_18. try clear R21_19. try clear R21_20. try clear R21_21. try clear R21_22. try clear R21_23. try clear R21_24. try clear R21_25. try clear R21_26. try clear R21_27. try clear DEF21. try clear HH21. try clear HQ21. try clear ES21. try clear DEFref_21. try clear DEFA_21. try clear DEFd3_21. try clear DEFd4_21.
  eapply (seg13 fx22 R0 R R22 M M22 model model18 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R22_1 R22_2 R22_3 R22_4 R22_8 R22_9 R22_10 R22_11 R22_18 R22_19 R22_20 R22_21 R22_22 R22_23 R22_24 R22_25 R22_26 R22_27 c22_Sm424 c22_Sm432 c22_Sm360 c22_Sm368 c22_Sm376 c22_Sm56 c22_Sm64 c22_Sm72 c22_Sm80 c22_Sm88 c22_Sm96 c22_Sm104 c22_Sm112 c22_Sm120 c22_Sm128 c22_Sm136 c22_Sm144 c22_Sm152 c22_Sm8 c22_Sm16 c22_Sm464w1 c22_Sm408w1 c22_Sm280w1 c22_Sm248w1 c22_Sm216w1 c22_Sm192 c22_Sm200 c22_Sm184w1 c22_Sm160 c22_Sm168 c22_Sm48w1 c22_Om128z8 c22_Om80z12 c22_Op0 c22_Op8 c22_Fp24 c22_Fp32 c22_Fp40 c22_Fp48 c22_Fp56 c22_Fp64w1 c22_Fp65w1 c22_Fp16w4 c22_Fp8 c22_Fp0 c22_Om8 c22_Om40 c22_Om48 c22_Om56 c22_Om64 c22_Om68w4 c22_Om16 c22_Om120 c22_Om24 c22_Om32 c22_Om88 c22_Om104 c22_Om112 c22_Om96 ES22 DEF22 DEFref_22 DEFA_22 DEFd3_22 DEFd4_22 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH22 MOK18 MBV18 HQ22 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S12.
