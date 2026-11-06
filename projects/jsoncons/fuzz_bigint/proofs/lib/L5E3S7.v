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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S8.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S7.
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
Let seg8 := L5E3S8.seg8 L HI LY LYX HIok.

Lemma seg7 (fx10 : FPState) (R0 R R10 : bvmap 5 word) (M M10 : word -> option byte) (model model8 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A msg ref u0_9 u3_19 u3_18 : Z) :
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
  0 <= u0_9 < 2 ^ 64 ->
  0 <= u3_19 < 2 ^ 64 ->
  0 <= u3_18 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R10 (reg 1) = Z_to_bv 64 136368 ->
  (* [comment removed for export] *) getr R10 (reg 2) = Z_to_bv 64 (S - 896) ->
  (* [comment removed for export] *) getr R10 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R10 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R10 (reg 8) = Z_to_bv 64 (A + 128) ->
  (* [comment removed for export] *) getr R10 (reg 9) = Z_to_bv 64 u0_9 ->
  (* [comment removed for export] *) getr R10 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R10 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R10 (reg 12) = Z_to_bv 64 257624 ->
  (* [comment removed for export] *) getr R10 (reg 18) = Z_to_bv 64 u3_18 ->
  (* [comment removed for export] *) getr R10 (reg 19) = Z_to_bv 64 u3_19 ->
  (* [comment removed for export] *) getr R10 (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M10 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M10 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (msg + 41) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 msg 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (msg + 8) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (msg + 16) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (msg + 24) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (msg + 32) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (msg + 40) 48 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 880) msg ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 888) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (S - 896) 49 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M10 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M10 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M10 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M10 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M10 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M10 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M10 ref 66 ->
  (* [comment removed for export] *) L5.defined M10 msg 48 ->
  (* [comment removed for export] *) L5.defined M10 A 144 ->
  (* [comment removed for export] *) L5.defined M10 d1 64 ->
  (* [comment removed for export] *) L5.defined M10 d2 64 ->
  (* [comment removed for export] *) L5.defined M10 d3 64 ->
  (* [comment removed for export] *) L5.defined M10 d4 64 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L msg 48 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d1 64 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (ref + 66 <= msg \/ msg + 48 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d1 \/ d1 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d2 \/ d2 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d3 \/ d3 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d4 \/ d4 + 64 <= ref) ->
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
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 msg 48 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M10 (m_vmmaps model8) ->
  (* [comment removed for export] *) model_ok model8 ->
  (* [comment removed for export] *) model_but_vm model model8 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M10 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx10 R10 136368 M10 model8) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 Wu3_19 Wu3_18 R10_1 R10_2 R10_3 R10_4 R10_8 R10_9 R10_10 R10_11 R10_12 R10_18 R10_19 R10_20 c10_Sm840 c10_Sm848 c10_Sm856 c10_Sm864 c10_Sm872 c10_Sm776 c10_Sm784 c10_Sm792 c10_Sm800 c10_Sm472 c10_Sm480 c10_Sm488 c10_Sm496 c10_Sm504 c10_Sm512 c10_Sm520 c10_Sm528 c10_Sm536 c10_Sm544 c10_Sm552 c10_Sm560 c10_Sm568 c10_Sm424 c10_Sm432 c10_Sm360 c10_Sm368 c10_Sm376 c10_Sm56 c10_Sm64 c10_Sm72 c10_Sm80 c10_Sm88 c10_Sm96 c10_Sm104 c10_Sm112 c10_Sm120 c10_Sm128 c10_Sm136 c10_Sm144 c10_Sm152 c10_Sm8 c10_Sm16 c10_Sm696w1 c10_Sm664w1 c10_Sm640 c10_Sm648 c10_Sm632w1 c10_Sm608 c10_Sm616 c10_Sm600w1 c10_Sm464w1 c10_Sm408w1 c10_Sm280w1 c10_Sm248w1 c10_Sm216w1 c10_Sm192 c10_Sm200 c10_Sm184w1 c10_Sm160 c10_Sm168 c10_Sm48w1 c10_Om128z8 c10_Om80z12 c10_Gp41w1 c10_Gp0 c10_Gp8 c10_Gp16 c10_Gp24 c10_Gp32 c10_Gp40w1 c10_Sm880 c10_Sm888 c10_Sm896 c10_Op0 c10_Op8 c10_Fp24 c10_Fp32 c10_Fp40 c10_Fp48 c10_Fp56 c10_Fp64w1 c10_Fp65w1 c10_Fp16w4 c10_Fp8 c10_Fp0 c10_Om8 c10_Om40 c10_Om48 c10_Om56 c10_Om64 c10_Om68w4 c10_Om16 c10_Om120 c10_Om24 c10_Om32 c10_Om88 c10_Om104 c10_Om112 c10_Om96 ES10 DEF10 DEFref_10 DEFmsg_10 DEFA_10 DEFd1_10 DEFd2_10 DEFd3_10 DEFd4_10 BR_ref BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_msg AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_msg FRSH_A HH10 MOK8 MBV8 HQ10 KE.
  pose proof MOK8 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_msg as (B0_msg & B1_msg & B2_msg & B3_msg & B4_msg). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_msg. unfold hl_ceil in B4_msg.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES10 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES10 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M10 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p1_conc fx10 R10 M10 (S - 896) (A + 128) msg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx11 & R11 & M11 & MS11 & K11 & R11_1 & R11_2 & R11_9 & R11_10 & R11_11 & FR11 & GR11).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF10); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF10); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_10); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_10); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFmsg_10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFmsg_10); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFmsg_10 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. apply (L5.defined_sub _ _ _ _ _ DEFmsg_10); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c10_Sm896 | cellfix c10_Sm896]. }
  { (* [comment removed for export] *) first [exact c10_Sm880 | cellfix c10_Sm880]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS11.
  (* [comment removed for export] *)
  assert (AG11: forall a k, ((a + k <= (S - 960) \/ (S - 896) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M10 M11 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR11; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R11_1n: getr R11 (reg 1) = Z_to_bv 64 136400) by (rewrite R11_1; f_equal; ring). clear R11_1. rename R11_1n into R11_1.
  assert (R11_2n: getr R11 (reg 2) = Z_to_bv 64 (S - 896)) by (rewrite R11_2; f_equal; ring). clear R11_2. rename R11_2n into R11_2.
  assert (R11_3: getr R11 (reg 3) = Z_to_bv 64 67584) by (kin K11 3%nat; exact R10_3).
  assert (R11_4: getr R11 (reg 4) = Z_to_bv 64 459832) by (kin K11 4%nat; exact R10_4).
  assert (R11_8: getr R11 (reg 8) = Z_to_bv 64 (A + 128)) by (kin K11 8%nat; exact R10_8).
  assert (R11_9n: getr R11 (reg 9) = Z_to_bv 64 (A + 96)) by (rewrite R11_9; f_equal; ring). clear R11_9. rename R11_9n into R11_9.
  assert (R11_10n: getr R11 (reg 10) = Z_to_bv 64 msg) by (rewrite R11_10; f_equal; ring). clear R11_10. rename R11_10n into R11_10.
  assert (R11_11n: getr R11 (reg 11) = Z_to_bv 64 48) by (rewrite R11_11; f_equal; ring). clear R11_11. rename R11_11n into R11_11.
  assert (R11_12: getr R11 (reg 12) = Z_to_bv 64 257624) by (kin K11 12%nat; exact R10_12).
  assert (R11_18: getr R11 (reg 18) = Z_to_bv 64 u3_18) by (kin K11 18%nat; exact R10_18).
  assert (R11_19: getr R11 (reg 19) = Z_to_bv 64 u3_19) by (kin K11 19%nat; exact R10_19).
  assert (R11_20: getr R11 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K11 20%nat; exact R10_20).
  assert (c11_Sm840: L5.u64_at RSEGS M11 (S - 840) 135392) by (clear - AG11 c10_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm840]).
  assert (c11_Sm848: L5.u64_at RSEGS M11 (S - 848) (S + 64)) by (clear - AG11 c10_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm848]).
  assert (c11_Sm856: L5.u64_at RSEGS M11 (S - 856) w856) by (clear - AG11 c10_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm856]).
  assert (c11_Sm864: L5.u64_at RSEGS M11 (S - 864) w864) by (clear - AG11 c10_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm864]).
  assert (c11_Sm872: L5.u64_at RSEGS M11 (S - 872) w872) by (clear - AG11 c10_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm872]).
  assert (c11_Sm776: L5.u64_at RSEGS M11 (S - 776) 139520) by (clear - AG11 c10_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm776]).
  assert (c11_Sm784: L5.u64_at RSEGS M11 (S - 784) w784) by (clear - AG11 c10_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm784]).
  assert (c11_Sm792: L5.u64_at RSEGS M11 (S - 792) (S + 64)) by (clear - AG11 c10_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm792]).
  assert (c11_Sm800: L5.u64_at RSEGS M11 (S - 800) (S + 64)) by (clear - AG11 c10_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm800]).
  assert (c11_Sm472: L5.u64_at RSEGS M11 (S - 472) 142136) by (clear - AG11 c10_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm472]).
  assert (c11_Sm480: L5.u64_at RSEGS M11 (S - 480) (S + 64)) by (clear - AG11 c10_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm480]).
  assert (c11_Sm488: L5.u64_at RSEGS M11 (S - 488) w488) by (clear - AG11 c10_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm488]).
  assert (c11_Sm496: L5.u64_at RSEGS M11 (S - 496) (S + 64)) by (clear - AG11 c10_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm496]).
  assert (c11_Sm504: L5.u64_at RSEGS M11 (S - 504) w504) by (clear - AG11 c10_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm504]).
  assert (c11_Sm512: L5.u64_at RSEGS M11 (S - 512) w512) by (clear - AG11 c10_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm512]).
  assert (c11_Sm520: L5.u64_at RSEGS M11 (S - 520) w520) by (clear - AG11 c10_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm520]).
  assert (c11_Sm528: L5.u64_at RSEGS M11 (S - 528) w528) by (clear - AG11 c10_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm528]).
  assert (c11_Sm536: L5.u64_at RSEGS M11 (S - 536) w536) by (clear - AG11 c10_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm536]).
  assert (c11_Sm544: L5.u64_at RSEGS M11 (S - 544) w544) by (clear - AG11 c10_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm544]).
  assert (c11_Sm552: L5.u64_at RSEGS M11 (S - 552) w552) by (clear - AG11 c10_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm552]).
  assert (c11_Sm560: L5.u64_at RSEGS M11 (S - 560) w560) by (clear - AG11 c10_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm560]).
  assert (c11_Sm568: L5.u64_at RSEGS M11 (S - 568) w568) by (clear - AG11 c10_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm568]).
  assert (c11_Sm424: L5.u64_at RSEGS M11 (S - 424) 141264) by (clear - AG11 c10_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm424]).
  assert (c11_Sm432: L5.u64_at RSEGS M11 (S - 432) (S + 64)) by (clear - AG11 c10_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm432]).
  assert (c11_Sm360: L5.u64_at RSEGS M11 (S - 360) 139904) by (clear - AG11 c10_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm360]).
  assert (c11_Sm368: L5.u64_at RSEGS M11 (S - 368) (S + 64)) by (clear - AG11 c10_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm368]).
  assert (c11_Sm376: L5.u64_at RSEGS M11 (S - 376) (S - 48)) by (clear - AG11 c10_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm376]).
  assert (c11_Sm56: L5.u64_at RSEGS M11 (S - 56) 138528) by (clear - AG11 c10_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm56]).
  assert (c11_Sm64: L5.u64_at RSEGS M11 (S - 64) (S + 64)) by (clear - AG11 c10_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm64]).
  assert (c11_Sm72: L5.u64_at RSEGS M11 (S - 72) (U R0 9)) by (clear - AG11 c10_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm72]).
  assert (c11_Sm80: L5.u64_at RSEGS M11 (S - 80) (U R0 18)) by (clear - AG11 c10_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm80]).
  assert (c11_Sm88: L5.u64_at RSEGS M11 (S - 88) (U R0 19)) by (clear - AG11 c10_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm88]).
  assert (c11_Sm96: L5.u64_at RSEGS M11 (S - 96) (U R0 20)) by (clear - AG11 c10_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm96]).
  assert (c11_Sm104: L5.u64_at RSEGS M11 (S - 104) (U R0 21)) by (clear - AG11 c10_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm104]).
  assert (c11_Sm112: L5.u64_at RSEGS M11 (S - 112) (U R0 22)) by (clear - AG11 c10_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm112]).
  assert (c11_Sm120: L5.u64_at RSEGS M11 (S - 120) (U R0 23)) by (clear - AG11 c10_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm120]).
  assert (c11_Sm128: L5.u64_at RSEGS M11 (S - 128) (U R0 24)) by (clear - AG11 c10_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm128]).
  assert (c11_Sm136: L5.u64_at RSEGS M11 (S - 136) (U R0 25)) by (clear - AG11 c10_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm136]).
  assert (c11_Sm144: L5.u64_at RSEGS M11 (S - 144) (U R0 26)) by (clear - AG11 c10_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm144]).
  assert (c11_Sm152: L5.u64_at RSEGS M11 (S - 152) (U R0 27)) by (clear - AG11 c10_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm152]).
  assert (c11_Sm8: L5.u64_at RSEGS M11 (S - 8) 132608) by (clear - AG11 c10_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm8]).
  assert (c11_Sm16: L5.u64_at RSEGS M11 (S - 16) (U R0 8)) by (clear - AG11 c10_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm16]).
  assert (c11_Sm696w1: L5.u8_at RSEGS M11 (S - 696) fb696) by (clear - AG11 c10_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm696w1]).
  assert (c11_Sm664w1: L5.u8_at RSEGS M11 (S - 664) fb664) by (clear - AG11 c10_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm664w1]).
  assert (c11_Sm640: L5.u64_at RSEGS M11 (S - 640) d1) by (clear - AG11 c10_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm640]).
  assert (c11_Sm648: L5.u64_at RSEGS M11 (S - 648) 8) by (clear - AG11 c10_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm648]).
  assert (c11_Sm632w1: L5.u8_at RSEGS M11 (S - 632) fb632) by (clear - AG11 c10_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm632w1]).
  assert (c11_Sm608: L5.u64_at RSEGS M11 (S - 608) d2) by (clear - AG11 c10_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm608]).
  assert (c11_Sm616: L5.u64_at RSEGS M11 (S - 616) 8) by (clear - AG11 c10_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm616]).
  assert (c11_Sm600w1: L5.u8_at RSEGS M11 (S - 600) fb600) by (clear - AG11 c10_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm600w1]).
  assert (c11_Sm464w1: L5.u8_at RSEGS M11 (S - 464) fb464) by (clear - AG11 c10_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm464w1]).
  assert (c11_Sm408w1: L5.u8_at RSEGS M11 (S - 408) fb408) by (clear - AG11 c10_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm408w1]).
  assert (c11_Sm280w1: L5.u8_at RSEGS M11 (S - 280) fb280) by (clear - AG11 c10_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm280w1]).
  assert (c11_Sm248w1: L5.u8_at RSEGS M11 (S - 248) fb248) by (clear - AG11 c10_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm248w1]).
  assert (c11_Sm216w1: L5.u8_at RSEGS M11 (S - 216) fb216) by (clear - AG11 c10_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm216w1]).
  assert (c11_Sm192: L5.u64_at RSEGS M11 (S - 192) d3) by (clear - AG11 c10_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm192]).
  assert (c11_Sm200: L5.u64_at RSEGS M11 (S - 200) 8) by (clear - AG11 c10_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm200]).
  assert (c11_Sm184w1: L5.u8_at RSEGS M11 (S - 184) fb184) by (clear - AG11 c10_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm184w1]).
  assert (c11_Sm160: L5.u64_at RSEGS M11 (S - 160) d4) by (clear - AG11 c10_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm160]).
  assert (c11_Sm168: L5.u64_at RSEGS M11 (S - 168) 8) by (clear - AG11 c10_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm168]).
  assert (c11_Sm48w1: L5.u8_at RSEGS M11 (S - 48) fb48) by (clear - AG11 c10_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Sm48w1]).
  assert (c11_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M11 (A + i) 0)) by (clear - AG11 c10_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | apply c10_Om128z8; exact Hi]).
  assert (c11_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M11 ((A + 48) + i) 0)) by (clear - AG11 c10_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | apply c10_Om80z12; exact Hi]).
  assert (c11_Gp41w1: L5.u8_at RSEGS M11 (msg + 41) 0) by (clear - AG11 c10_Gp41w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Gp41w1]).
  assert (c11_Gp0: L5.u64_at RSEGS M11 msg 8028075845441778529) by (clear - AG11 c10_Gp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Gp0]).
  assert (c11_Gp8: L5.u64_at RSEGS M11 (msg + 8) 7863351059373564014) by (clear - AG11 c10_Gp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Gp8]).
  assert (c11_Gp16: L5.u64_at RSEGS M11 (msg + 16) 2838809733452757089) by (clear - AG11 c10_Gp16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Gp16]).
  assert (c11_Gp24: L5.u64_at RSEGS M11 (msg + 24) 2334102023183623712) by (clear - AG11 c10_Gp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Gp24]).
  assert (c11_Gp32: L5.u64_at RSEGS M11 (msg + 32) 4188416081412519009) by (clear - AG11 c10_Gp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Gp32]).
  assert (c11_Gp40w1: L5.u8_at RSEGS M11 (msg + 40) 48) by (clear - AG11 c10_Gp40w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Gp40w1]).
  assert (c11_Sm880: L5.u64_at RSEGS M11 (S - 880) msg) by (clear - AG11 c10_Sm880 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm880]).
  assert (c11_Sm888: L5.u64_at RSEGS M11 (S - 888) 41) by (clear - AG11 c10_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm888]).
  assert (c11_Sm896: L5.u64_at RSEGS M11 (S - 896) 49) by (clear - AG11 c10_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Sm896]).
  assert (c11_Op0: L5.u64_at RSEGS M11 (A + 128) 373272) by (clear - AG11 c10_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Op0]).
  assert (c11_Op8: L5.u64_at RSEGS M11 (A + 136) (ref + 24)) by (clear - AG11 c10_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Op8]).
  assert (c11_Fp24: L5.u64_at RSEGS M11 (ref + 24) 8028075845441778529) by (clear - AG11 c10_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp24]).
  assert (c11_Fp32: L5.u64_at RSEGS M11 (ref + 32) 7863351059373564014) by (clear - AG11 c10_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp32]).
  assert (c11_Fp40: L5.u64_at RSEGS M11 (ref + 40) 2838809733452757089) by (clear - AG11 c10_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp40]).
  assert (c11_Fp48: L5.u64_at RSEGS M11 (ref + 48) 2334102023183623712) by (clear - AG11 c10_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp48]).
  assert (c11_Fp56: L5.u64_at RSEGS M11 (ref + 56) 4188416081412519009) by (clear - AG11 c10_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp56]).
  assert (c11_Fp64w1: L5.u8_at RSEGS M11 (ref + 64) 48) by (clear - AG11 c10_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Fp64w1]).
  assert (c11_Fp65w1: L5.u8_at RSEGS M11 (ref + 65) 0) by (clear - AG11 c10_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M10 M11 _ _ _ (AG11 _ 1)); [lia | exact c10_Fp65w1]).
  assert (c11_Fp16w4: L5.u32_at RSEGS M11 (ref + 16) 0) by (clear - AG11 c10_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M10 M11 _ _ _ (AG11 _ 4)); [lia | exact c10_Fp16w4]).
  assert (c11_Fp8: L5.u64_at RSEGS M11 (ref + 8) 41) by (clear - AG11 c10_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp8]).
  assert (c11_Fp0: L5.u64_at RSEGS M11 ref 41) by (clear - AG11 c10_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Fp0]).
  assert (c11_Om8: L5.u64_at RSEGS M11 (A + 120) S) by (clear - AG11 c10_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om8]).
  assert (c11_Om40: L5.u64_at RSEGS M11 (A + 88) (A + 128)) by (clear - AG11 c10_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om40]).
  assert (c11_Om48: L5.u64_at RSEGS M11 (A + 80) 133016) by (clear - AG11 c10_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om48]).
  assert (c11_Om56: L5.u64_at RSEGS M11 (A + 72) 91560) by (clear - AG11 c10_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om56]).
  assert (c11_Om64: L5.u64_at RSEGS M11 (A + 64) 91699) by (clear - AG11 c10_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om64]).
  assert (c11_Om68w4: L5.u32_at RSEGS M11 (A + 60) 1) by (clear - AG11 c10_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M10 M11 _ _ _ (AG11 _ 4)); [lia | exact c10_Om68w4]).
  assert (c11_Om16: L5.u64_at RSEGS M11 (A + 112) 0) by (clear - AG11 c10_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om16]).
  assert (c11_Om120: L5.u64_at RSEGS M11 (A + 8) 1) by (clear - AG11 c10_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om120]).
  assert (c11_Om24: L5.u64_at RSEGS M11 (A + 104) 257624) by (clear - AG11 c10_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om24]).
  assert (c11_Om32: L5.u64_at RSEGS M11 (A + 96) 4849336966747728640) by (clear - AG11 c10_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om32]).
  assert (c11_Om88: L5.u64_at RSEGS M11 (A + 40) 142700) by (clear - AG11 c10_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om88]).
  assert (c11_Om104: L5.u64_at RSEGS M11 (A + 24) 253816) by (clear - AG11 c10_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om104]).
  assert (c11_Om112: L5.u64_at RSEGS M11 (A + 16) 373232) by (clear - AG11 c10_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om112]).
  assert (c11_Om96: L5.u64_at RSEGS M11 (A + 32) 142968) by (clear - AG11 c10_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M10 M11 _ _ _ (AG11 _ 8)); [lia | exact c10_Om96]).
  assert (STAT11: forall a, stat_rd av a -> M11 (Z_to_bv 64 a) = M10 (Z_to_bv 64 a)).
  { clear - FR11 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR11; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M10 M11 gd av uid rnd canary hw ES10 STAT11) as ES11.
  assert (DEF11: L5.defined M11 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR11 | exact DEF10]).
  assert (DEFref_11: L5.defined M11 ref 66) by (eapply L5.defined_grows; [exact GR11 | exact DEFref_10]).
  assert (DEFmsg_11: L5.defined M11 msg 48) by (eapply L5.defined_grows; [exact GR11 | exact DEFmsg_10]).
  assert (DEFA_11: L5.defined M11 A 144) by (eapply L5.defined_grows; [exact GR11 | exact DEFA_10]).
  assert (DEFd1_11: L5.defined M11 d1 64) by (eapply L5.defined_grows; [exact GR11 | exact DEFd1_10]).
  assert (DEFd2_11: L5.defined M11 d2 64) by (eapply L5.defined_grows; [exact GR11 | exact DEFd2_10]).
  assert (DEFd3_11: L5.defined M11 d3 64) by (eapply L5.defined_grows; [exact GR11 | exact DEFd3_10]).
  assert (DEFd4_11: L5.defined M11 d4 64) by (eapply L5.defined_grows; [exact GR11 | exact DEFd4_10]).
  assert (HH11: hi_heap HI ((ref, 66) :: (msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M11 (m_vmmaps model8)).
  { clear - HH10 GR11 FR11 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH10. lia. 2: exact GR11. intros a Ha.
    destruct (in_dec (S - 960) (S - 896) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR11; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ11: L5C.hpres L LB1 S 10240 XSF M M11).
  { clear - LBWF HQ10 FR11 GR11 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M10 M11 [((S - 960), 64)]). exact LBWF. lia. exact HQ10.
    { intros x Hx. apply FR11; intros Hin.
        apply (Hx ((S - 960), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR11.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG11 FR11 MS11. try clear STAT11. try clear K10.
  try clear c10_Sm840. try clear c10_Sm848. try clear c10_Sm856. try clear c10_Sm864. try clear c10_Sm872. try clear c10_Sm776. try clear c10_Sm784. try clear c10_Sm792. try clear c10_Sm800. try clear c10_Sm472. try clear c10_Sm480. try clear c10_Sm488. try clear c10_Sm496. try clear c10_Sm504. try clear c10_Sm512. try clear c10_Sm520. try clear c10_Sm528. try clear c10_Sm536. try clear c10_Sm544. try clear c10_Sm552. try clear c10_Sm560. try clear c10_Sm568. try clear c10_Sm424. try clear c10_Sm432. try clear c10_Sm360. try clear c10_Sm368. try clear c10_Sm376. try clear c10_Sm56. try clear c10_Sm64. try clear c10_Sm72. try clear c10_Sm80. try clear c10_Sm88. try clear c10_Sm96. try clear c10_Sm104. try clear c10_Sm112. try clear c10_Sm120. try clear c10_Sm128. try clear c10_Sm136. try clear c10_Sm144. try clear c10_Sm152. try clear c10_Sm8. try clear c10_Sm16. try clear c10_Sm696w1. try clear c10_Sm664w1. try clear c10_Sm640. try clear c10_Sm648. try clear c10_Sm632w1. try clear c10_Sm608. try clear c10_Sm616. try clear c10_Sm600w1. try clear c10_Sm464w1. try clear c10_Sm408w1. try clear c10_Sm280w1. try clear c10_Sm248w1. try clear c10_Sm216w1. try clear c10_Sm192. try clear c10_Sm200. try clear c10_Sm184w1. try clear c10_Sm160. try clear c10_Sm168. try clear c10_Sm48w1. try clear c10_Om128z8. try clear c10_Om80z12. try clear c10_Gp41w1. try clear c10_Gp0. try clear c10_Gp8. try clear c10_Gp16. try clear c10_Gp24. try clear c10_Gp32. try clear c10_Gp40w1. try clear c10_Sm880. try clear c10_Sm888. try clear c10_Sm896. try clear c10_Op0. try clear c10_Op8. try clear c10_Fp24. try clear c10_Fp32. try clear c10_Fp40. try clear c10_Fp48. try clear c10_Fp56. try clear c10_Fp64w1. try clear c10_Fp65w1. try clear c10_Fp16w4. try clear c10_Fp8. try clear c10_Fp0. try clear c10_Om8. try clear c10_Om40. try clear c10_Om48. try clear c10_Om56. try clear c10_Om64. try clear c10_Om68w4. try clear c10_Om16. try clear c10_Om120. try clear c10_Om24. try clear c10_Om32. try clear c10_Om88. try clear c10_Om104. try clear c10_Om112. try clear c10_Om96. try clear R10_1. try clear R10_2. try clear R10_3. try clear R10_4. try clear R10_8. try clear R10_9. try clear R10_10. try clear R10_11. try clear R10_12. try clear R10_18. try clear R10_19. try clear R10_20. try clear DEF10. try clear HH10. try clear HQ10. try clear ES10. try clear DEFref_10. try clear DEFmsg_10. try clear DEFA_10. try clear DEFd1_10. try clear DEFd2_10. try clear DEFd3_10. try clear DEFd4_10.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx11 R11 M11 model8 ((ref, 66) :: (msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) msg 48 K) as HC.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH11.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - right; left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R11_10.
  - rewrite L5CoreKit.L5K.rl4. exact R11_4.
  - rewrite L5CoreKit.L5K.rl1, R11_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R11_2 A16 DEF11 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R11_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-56) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M11 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF11. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R12 M12 model12 RP12 [PRES12 _] MBVn HH12.
    rewrite L5CoreKit.L5K.rl1, R11_1.
    cbn [lb_remove fst app] in PRES12, HH12.
    rewrite (proj2 (Z.eqb_neq ref msg) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref B0_msg B1_msg B3_msg B4_msg AP_ref_msg)) in PRES12, HH12.
    rewrite Z.eqb_refl in PRES12, HH12.
    rewrite L5CoreKit.L5K.rl2, R11_2, BG.unsigned_lit in PRES12 by (kl SLO SHI STOP).
    match type of PRES12 with heap_pres_core _ _ ?x _ _ => replace x with (S - 896) in PRES12 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 896) M11 M12 PRES12) as HP12. rewrite (ly_stack L LY) in HP12. unfold HEAP_STACK in HP12.
    assert (AGS12: forall a k, ((S - 896) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M11 M12 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP12 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP12. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_ref: L5C.agree_on M11 M12 ref 66).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_A: L5C.agree_on M11 M12 A 144).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_d1: L5C.agree_on M11 M12 d1 64).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d1. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_d2: L5C.agree_on M11 M12 d2 64).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d2. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_d3: L5C.agree_on M11 M12 d3 64).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB12_d4: L5C.agree_on M11 M12 d4 64).
    { clear - HP12 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP12. right; right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT12: forall a, stat_rd av a -> M12 (Z_to_bv 64 a) = M11 (Z_to_bv 64 a)).
    { clear - HP12 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 896) 8224 [] M11 M12 HP12). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (statics_landed_keep M11 M12 gd av uid rnd canary hw ES11 STAT12) as ES12.
    assert (DEF12: L5.defined M12 (S - 10240) 10240).
    { clear - HP12 DEF11 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 896) 8224 [] M11 M12). exact HP12. lia. lia. lia. lia. exact DEF11. }
    assert (DEFref_12: L5.defined M12 ref 66) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_ref | exact DEFref_11]).
    assert (DEFA_12: L5.defined M12 A 144) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_A | exact DEFA_11]).
    assert (DEFd1_12: L5.defined M12 d1 64) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_d1 | exact DEFd1_11]).
    assert (DEFd2_12: L5.defined M12 d2 64) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_d2 | exact DEFd2_11]).
    assert (DEFd3_12: L5.defined M12 d3 64) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_d3 | exact DEFd3_11]).
    assert (DEFd4_12: L5.defined M12 d4 64) by (eapply (L5C.defined_agree M11 M12); [exact AGB12_d4 | exact DEFd4_11]).
    assert (MOK12: model_ok model12).
    { destruct MOK8 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK12 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV8 MBVn) as MBV12. clear MBVn MBV8.
    assert (RPi12: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R12 (reg i) = getr R11 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R11 R12 i RP12). exact Hi. }
    assert (R12_2: getr R12 (reg 2) = Z_to_bv 64 (S - 896)) by (rewrite (RPi12 2%nat) by inl; exact R11_2).
    assert (R12_3: getr R12 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi12 3%nat) by inl; exact R11_3).
    assert (R12_4: getr R12 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi12 4%nat) by inl; exact R11_4).
    assert (R12_8: getr R12 (reg 8) = Z_to_bv 64 (A + 128)) by (rewrite (RPi12 8%nat) by inl; exact R11_8).
    assert (R12_9: getr R12 (reg 9) = Z_to_bv 64 (A + 96)) by (rewrite (RPi12 9%nat) by inl; exact R11_9).
    assert (R12_18: getr R12 (reg 18) = Z_to_bv 64 u3_18) by (rewrite (RPi12 18%nat) by inl; exact R11_18).
    assert (R12_19: getr R12 (reg 19) = Z_to_bv 64 u3_19) by (rewrite (RPi12 19%nat) by inl; exact R11_19).
    assert (R12_20: getr R12 (reg 20) = Z_to_bv 64 (S - 584)) by (rewrite (RPi12 20%nat) by inl; exact R11_20).
    assert (c12_Sm840: L5.u64_at RSEGS M12 (S - 840) 135392) by (clear - AGS12 c11_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm840]).
    assert (c12_Sm848: L5.u64_at RSEGS M12 (S - 848) (S + 64)) by (clear - AGS12 c11_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm848]).
    assert (c12_Sm856: L5.u64_at RSEGS M12 (S - 856) w856) by (clear - AGS12 c11_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm856]).
    assert (c12_Sm864: L5.u64_at RSEGS M12 (S - 864) w864) by (clear - AGS12 c11_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm864]).
    assert (c12_Sm872: L5.u64_at RSEGS M12 (S - 872) w872) by (clear - AGS12 c11_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm872]).
    assert (c12_Sm776: L5.u64_at RSEGS M12 (S - 776) 139520) by (clear - AGS12 c11_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm776]).
    assert (c12_Sm784: L5.u64_at RSEGS M12 (S - 784) w784) by (clear - AGS12 c11_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm784]).
    assert (c12_Sm792: L5.u64_at RSEGS M12 (S - 792) (S + 64)) by (clear - AGS12 c11_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm792]).
    assert (c12_Sm800: L5.u64_at RSEGS M12 (S - 800) (S + 64)) by (clear - AGS12 c11_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm800]).
    assert (c12_Sm472: L5.u64_at RSEGS M12 (S - 472) 142136) by (clear - AGS12 c11_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm472]).
    assert (c12_Sm480: L5.u64_at RSEGS M12 (S - 480) (S + 64)) by (clear - AGS12 c11_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm480]).
    assert (c12_Sm488: L5.u64_at RSEGS M12 (S - 488) w488) by (clear - AGS12 c11_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm488]).
    assert (c12_Sm496: L5.u64_at RSEGS M12 (S - 496) (S + 64)) by (clear - AGS12 c11_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm496]).
    assert (c12_Sm504: L5.u64_at RSEGS M12 (S - 504) w504) by (clear - AGS12 c11_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm504]).
    assert (c12_Sm512: L5.u64_at RSEGS M12 (S - 512) w512) by (clear - AGS12 c11_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm512]).
    assert (c12_Sm520: L5.u64_at RSEGS M12 (S - 520) w520) by (clear - AGS12 c11_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm520]).
    assert (c12_Sm528: L5.u64_at RSEGS M12 (S - 528) w528) by (clear - AGS12 c11_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm528]).
    assert (c12_Sm536: L5.u64_at RSEGS M12 (S - 536) w536) by (clear - AGS12 c11_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm536]).
    assert (c12_Sm544: L5.u64_at RSEGS M12 (S - 544) w544) by (clear - AGS12 c11_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm544]).
    assert (c12_Sm552: L5.u64_at RSEGS M12 (S - 552) w552) by (clear - AGS12 c11_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm552]).
    assert (c12_Sm560: L5.u64_at RSEGS M12 (S - 560) w560) by (clear - AGS12 c11_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm560]).
    assert (c12_Sm568: L5.u64_at RSEGS M12 (S - 568) w568) by (clear - AGS12 c11_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm568]).
    assert (c12_Sm424: L5.u64_at RSEGS M12 (S - 424) 141264) by (clear - AGS12 c11_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm424]).
    assert (c12_Sm432: L5.u64_at RSEGS M12 (S - 432) (S + 64)) by (clear - AGS12 c11_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm432]).
    assert (c12_Sm360: L5.u64_at RSEGS M12 (S - 360) 139904) by (clear - AGS12 c11_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm360]).
    assert (c12_Sm368: L5.u64_at RSEGS M12 (S - 368) (S + 64)) by (clear - AGS12 c11_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm368]).
    assert (c12_Sm376: L5.u64_at RSEGS M12 (S - 376) (S - 48)) by (clear - AGS12 c11_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm376]).
    assert (c12_Sm56: L5.u64_at RSEGS M12 (S - 56) 138528) by (clear - AGS12 c11_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm56]).
    assert (c12_Sm64: L5.u64_at RSEGS M12 (S - 64) (S + 64)) by (clear - AGS12 c11_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm64]).
    assert (c12_Sm72: L5.u64_at RSEGS M12 (S - 72) (U R0 9)) by (clear - AGS12 c11_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm72]).
    assert (c12_Sm80: L5.u64_at RSEGS M12 (S - 80) (U R0 18)) by (clear - AGS12 c11_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm80]).
    assert (c12_Sm88: L5.u64_at RSEGS M12 (S - 88) (U R0 19)) by (clear - AGS12 c11_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm88]).
    assert (c12_Sm96: L5.u64_at RSEGS M12 (S - 96) (U R0 20)) by (clear - AGS12 c11_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm96]).
    assert (c12_Sm104: L5.u64_at RSEGS M12 (S - 104) (U R0 21)) by (clear - AGS12 c11_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm104]).
    assert (c12_Sm112: L5.u64_at RSEGS M12 (S - 112) (U R0 22)) by (clear - AGS12 c11_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm112]).
    assert (c12_Sm120: L5.u64_at RSEGS M12 (S - 120) (U R0 23)) by (clear - AGS12 c11_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm120]).
    assert (c12_Sm128: L5.u64_at RSEGS M12 (S - 128) (U R0 24)) by (clear - AGS12 c11_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm128]).
    assert (c12_Sm136: L5.u64_at RSEGS M12 (S - 136) (U R0 25)) by (clear - AGS12 c11_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm136]).
    assert (c12_Sm144: L5.u64_at RSEGS M12 (S - 144) (U R0 26)) by (clear - AGS12 c11_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm144]).
    assert (c12_Sm152: L5.u64_at RSEGS M12 (S - 152) (U R0 27)) by (clear - AGS12 c11_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm152]).
    assert (c12_Sm8: L5.u64_at RSEGS M12 (S - 8) 132608) by (clear - AGS12 c11_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm8]).
    assert (c12_Sm16: L5.u64_at RSEGS M12 (S - 16) (U R0 8)) by (clear - AGS12 c11_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm16]).
    assert (c12_Sm696w1: L5.u8_at RSEGS M12 (S - 696) fb696) by (clear - AGS12 c11_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm696w1]).
    assert (c12_Sm664w1: L5.u8_at RSEGS M12 (S - 664) fb664) by (clear - AGS12 c11_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm664w1]).
    assert (c12_Sm640: L5.u64_at RSEGS M12 (S - 640) d1) by (clear - AGS12 c11_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm640]).
    assert (c12_Sm648: L5.u64_at RSEGS M12 (S - 648) 8) by (clear - AGS12 c11_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm648]).
    assert (c12_Sm632w1: L5.u8_at RSEGS M12 (S - 632) fb632) by (clear - AGS12 c11_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm632w1]).
    assert (c12_Sm608: L5.u64_at RSEGS M12 (S - 608) d2) by (clear - AGS12 c11_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm608]).
    assert (c12_Sm616: L5.u64_at RSEGS M12 (S - 616) 8) by (clear - AGS12 c11_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm616]).
    assert (c12_Sm600w1: L5.u8_at RSEGS M12 (S - 600) fb600) by (clear - AGS12 c11_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm600w1]).
    assert (c12_Sm464w1: L5.u8_at RSEGS M12 (S - 464) fb464) by (clear - AGS12 c11_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm464w1]).
    assert (c12_Sm408w1: L5.u8_at RSEGS M12 (S - 408) fb408) by (clear - AGS12 c11_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm408w1]).
    assert (c12_Sm280w1: L5.u8_at RSEGS M12 (S - 280) fb280) by (clear - AGS12 c11_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm280w1]).
    assert (c12_Sm248w1: L5.u8_at RSEGS M12 (S - 248) fb248) by (clear - AGS12 c11_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm248w1]).
    assert (c12_Sm216w1: L5.u8_at RSEGS M12 (S - 216) fb216) by (clear - AGS12 c11_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm216w1]).
    assert (c12_Sm192: L5.u64_at RSEGS M12 (S - 192) d3) by (clear - AGS12 c11_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm192]).
    assert (c12_Sm200: L5.u64_at RSEGS M12 (S - 200) 8) by (clear - AGS12 c11_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm200]).
    assert (c12_Sm184w1: L5.u8_at RSEGS M12 (S - 184) fb184) by (clear - AGS12 c11_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm184w1]).
    assert (c12_Sm160: L5.u64_at RSEGS M12 (S - 160) d4) by (clear - AGS12 c11_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm160]).
    assert (c12_Sm168: L5.u64_at RSEGS M12 (S - 168) 8) by (clear - AGS12 c11_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm168]).
    assert (c12_Sm48w1: L5.u8_at RSEGS M12 (S - 48) fb48) by (clear - AGS12 c11_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M11 M12 _ _ _ (AGS12 _ 1)); [lia | exact c11_Sm48w1]).
    assert (c12_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M12 (A + i) 0)) by (clear - AGB12_A c11_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB12_A); [lia | apply c11_Om128z8; exact Hi]).
    assert (c12_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M12 ((A + 48) + i) 0)) by (clear - AGB12_A c11_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB12_A); [lia | apply c11_Om80z12; exact Hi]).
    assert (c12_Sm880: L5.u64_at RSEGS M12 (S - 880) msg) by (clear - AGS12 c11_Sm880 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm880]).
    assert (c12_Sm888: L5.u64_at RSEGS M12 (S - 888) 41) by (clear - AGS12 c11_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm888]).
    assert (c12_Sm896: L5.u64_at RSEGS M12 (S - 896) 49) by (clear - AGS12 c11_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M11 M12 _ _ _ (AGS12 _ 8)); [lia | exact c11_Sm896]).
    assert (c12_Op0: L5.u64_at RSEGS M12 (A + 128) 373272) by (clear - AGB12_A c11_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Op0]).
    assert (c12_Op8: L5.u64_at RSEGS M12 (A + 136) (ref + 24)) by (clear - AGB12_A c11_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Op8]).
    assert (c12_Fp24: L5.u64_at RSEGS M12 (ref + 24) 8028075845441778529) by (clear - AGB12_ref c11_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp24]).
    assert (c12_Fp32: L5.u64_at RSEGS M12 (ref + 32) 7863351059373564014) by (clear - AGB12_ref c11_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp32]).
    assert (c12_Fp40: L5.u64_at RSEGS M12 (ref + 40) 2838809733452757089) by (clear - AGB12_ref c11_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp40]).
    assert (c12_Fp48: L5.u64_at RSEGS M12 (ref + 48) 2334102023183623712) by (clear - AGB12_ref c11_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp48]).
    assert (c12_Fp56: L5.u64_at RSEGS M12 (ref + 56) 4188416081412519009) by (clear - AGB12_ref c11_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp56]).
    assert (c12_Fp64w1: L5.u8_at RSEGS M12 (ref + 64) 48) by (clear - AGB12_ref c11_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp64w1]).
    assert (c12_Fp65w1: L5.u8_at RSEGS M12 (ref + 65) 0) by (clear - AGB12_ref c11_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp65w1]).
    assert (c12_Fp16w4: L5.u32_at RSEGS M12 (ref + 16) 0) by (clear - AGB12_ref c11_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb32 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp16w4]).
    assert (c12_Fp8: L5.u64_at RSEGS M12 (ref + 8) 41) by (clear - AGB12_ref c11_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp8]).
    assert (c12_Fp0: L5.u64_at RSEGS M12 ref 41) by (clear - AGB12_ref c11_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB12_ref); [lia | exact c11_Fp0]).
    assert (c12_Om8: L5.u64_at RSEGS M12 (A + 120) S) by (clear - AGB12_A c11_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om8]).
    assert (c12_Om40: L5.u64_at RSEGS M12 (A + 88) (A + 128)) by (clear - AGB12_A c11_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om40]).
    assert (c12_Om48: L5.u64_at RSEGS M12 (A + 80) 133016) by (clear - AGB12_A c11_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om48]).
    assert (c12_Om56: L5.u64_at RSEGS M12 (A + 72) 91560) by (clear - AGB12_A c11_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om56]).
    assert (c12_Om64: L5.u64_at RSEGS M12 (A + 64) 91699) by (clear - AGB12_A c11_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om64]).
    assert (c12_Om68w4: L5.u32_at RSEGS M12 (A + 60) 1) by (clear - AGB12_A c11_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb32 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om68w4]).
    assert (c12_Om16: L5.u64_at RSEGS M12 (A + 112) 0) by (clear - AGB12_A c11_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om16]).
    assert (c12_Om120: L5.u64_at RSEGS M12 (A + 8) 1) by (clear - AGB12_A c11_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om120]).
    assert (c12_Om24: L5.u64_at RSEGS M12 (A + 104) 257624) by (clear - AGB12_A c11_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om24]).
    assert (c12_Om32: L5.u64_at RSEGS M12 (A + 96) 4849336966747728640) by (clear - AGB12_A c11_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om32]).
    assert (c12_Om88: L5.u64_at RSEGS M12 (A + 40) 142700) by (clear - AGB12_A c11_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om88]).
    assert (c12_Om104: L5.u64_at RSEGS M12 (A + 24) 253816) by (clear - AGB12_A c11_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om104]).
    assert (c12_Om112: L5.u64_at RSEGS M12 (A + 16) 373232) by (clear - AGB12_A c11_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om112]).
    assert (c12_Om96: L5.u64_at RSEGS M12 (A + 32) 142968) by (clear - AGB12_A c11_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB12_A); [lia | exact c11_Om96]).
    assert (HQ12: L5C.hpres L LB1 S 10240 XSF M M12).
    { clear - LBWF HQ11 HP12 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 896) 8224 [] M M11 M12). exact LBWF. lia. lia. exact HQ11. exact HP12. intros bb Hbb; right; right; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS12 STAT12 PRES12 RP12 RPi12 HP12 AGB12_ref AGB12_A AGB12_d1 AGB12_d2 AGB12_d3 AGB12_d4.
    try clear c11_Sm840 c11_Sm848 c11_Sm856 c11_Sm864 c11_Sm872 c11_Sm776 c11_Sm784 c11_Sm792 c11_Sm800 c11_Sm472 c11_Sm480 c11_Sm488 c11_Sm496 c11_Sm504 c11_Sm512 c11_Sm520 c11_Sm528 c11_Sm536 c11_Sm544 c11_Sm552 c11_Sm560 c11_Sm568 c11_Sm424 c11_Sm432 c11_Sm360 c11_Sm368 c11_Sm376 c11_Sm56 c11_Sm64 c11_Sm72 c11_Sm80 c11_Sm88 c11_Sm96 c11_Sm104 c11_Sm112 c11_Sm120 c11_Sm128 c11_Sm136 c11_Sm144 c11_Sm152 c11_Sm8 c11_Sm16 c11_Sm696w1 c11_Sm664w1 c11_Sm640 c11_Sm648 c11_Sm632w1 c11_Sm608 c11_Sm616 c11_Sm600w1 c11_Sm464w1 c11_Sm408w1 c11_Sm280w1 c11_Sm248w1 c11_Sm216w1 c11_Sm192 c11_Sm200 c11_Sm184w1 c11_Sm160 c11_Sm168 c11_Sm48w1 c11_Om128z8 c11_Om80z12 c11_Gp41w1 c11_Gp0 c11_Gp8 c11_Gp16 c11_Gp24 c11_Gp32 c11_Gp40w1 c11_Sm880 c11_Sm888 c11_Sm896 c11_Op0 c11_Op8 c11_Fp24 c11_Fp32 c11_Fp40 c11_Fp48 c11_Fp56 c11_Fp64w1 c11_Fp65w1 c11_Fp16w4 c11_Fp8 c11_Fp0 c11_Om8 c11_Om40 c11_Om48 c11_Om56 c11_Om64 c11_Om68w4 c11_Om16 c11_Om120 c11_Om24 c11_Om32 c11_Om88 c11_Om104 c11_Om112 c11_Om96 R11_1 R11_2 R11_3 R11_4 R11_8 R11_9 R11_10 R11_11 R11_12 R11_18 R11_19 R11_20 DEF11 HH11 HQ11 ES11 K11 DEFref_11 DEFmsg_11 DEFA_11 DEFd1_11 DEFd2_11 DEFd3_11 DEFd4_11.
    eapply (seg8 fx11 R0 R R12 M M12 model model12 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref u3_19 u3_18 msg HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu3_19 Wu3_18 R12_2 R12_3 R12_4 R12_8 R12_9 R12_18 R12_19 R12_20 c12_Sm840 c12_Sm848 c12_Sm856 c12_Sm864 c12_Sm872 c12_Sm776 c12_Sm784 c12_Sm792 c12_Sm800 c12_Sm472 c12_Sm480 c12_Sm488 c12_Sm496 c12_Sm504 c12_Sm512 c12_Sm520 c12_Sm528 c12_Sm536 c12_Sm544 c12_Sm552 c12_Sm560 c12_Sm568 c12_Sm424 c12_Sm432 c12_Sm360 c12_Sm368 c12_Sm376 c12_Sm56 c12_Sm64 c12_Sm72 c12_Sm80 c12_Sm88 c12_Sm96 c12_Sm104 c12_Sm112 c12_Sm120 c12_Sm128 c12_Sm136 c12_Sm144 c12_Sm152 c12_Sm8 c12_Sm16 c12_Sm696w1 c12_Sm664w1 c12_Sm640 c12_Sm648 c12_Sm632w1 c12_Sm608 c12_Sm616 c12_Sm600w1 c12_Sm464w1 c12_Sm408w1 c12_Sm280w1 c12_Sm248w1 c12_Sm216w1 c12_Sm192 c12_Sm200 c12_Sm184w1 c12_Sm160 c12_Sm168 c12_Sm48w1 c12_Om128z8 c12_Om80z12 c12_Sm880 c12_Sm888 c12_Sm896 c12_Op0 c12_Op8 c12_Fp24 c12_Fp32 c12_Fp40 c12_Fp48 c12_Fp56 c12_Fp64w1 c12_Fp65w1 c12_Fp16w4 c12_Fp8 c12_Fp0 c12_Om8 c12_Om40 c12_Om48 c12_Om56 c12_Om64 c12_Om68w4 c12_Om16 c12_Om120 c12_Om24 c12_Om32 c12_Om88 c12_Om104 c12_Om112 c12_Om96 ES12 DEF12 DEFref_12 DEFA_12 DEFd1_12 DEFd2_12 DEFd3_12 DEFd4_12 BR_ref BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH12 MOK12 MBV12 HQ12 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S7.
