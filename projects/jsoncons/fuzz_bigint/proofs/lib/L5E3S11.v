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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S12.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S11.
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
Let seg12 := L5E3S12.seg12 L HI LY LYX HIok.

Lemma seg11 (fx17 : FPState) (R0 R R18 : bvmap 5 word) (M M18 : word -> option byte) (model model18 : Model) (K : TSet)
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
  (* [comment removed for export] *) getr R18 (reg 2) = Z_to_bv 64 (S - 768) ->
  (* [comment removed for export] *) getr R18 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R18 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R18 (reg 8) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R18 (reg 9) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R18 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R18 (reg 19) = Z_to_bv 64 w872 ->
  (* [comment removed for export] *) getr R18 (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M18 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M18 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M18 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M18 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M18 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M18 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M18 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M18 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M18 ref 66 ->
  (* [comment removed for export] *) L5.defined M18 A 144 ->
  (* [comment removed for export] *) L5.defined M18 d3 64 ->
  (* [comment removed for export] *) L5.defined M18 d4 64 ->
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
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M18 (m_vmmaps model18) ->
  (* [comment removed for export] *) model_ok model18 ->
  (* [comment removed for export] *) model_but_vm model model18 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M18 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx17 R18 140348 M18 model18) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R18_2 R18_3 R18_4 R18_8 R18_9 R18_18 R18_19 R18_20 c18_Sm472 c18_Sm480 c18_Sm488 c18_Sm496 c18_Sm504 c18_Sm512 c18_Sm520 c18_Sm528 c18_Sm536 c18_Sm544 c18_Sm552 c18_Sm560 c18_Sm568 c18_Sm424 c18_Sm432 c18_Sm360 c18_Sm368 c18_Sm376 c18_Sm56 c18_Sm64 c18_Sm72 c18_Sm80 c18_Sm88 c18_Sm96 c18_Sm104 c18_Sm112 c18_Sm120 c18_Sm128 c18_Sm136 c18_Sm144 c18_Sm152 c18_Sm8 c18_Sm16 c18_Sm696w1 c18_Sm664w1 c18_Sm640 c18_Sm648 c18_Sm632w1 c18_Sm608 c18_Sm616 c18_Sm600w1 c18_Sm464w1 c18_Sm408w1 c18_Sm280w1 c18_Sm248w1 c18_Sm216w1 c18_Sm192 c18_Sm200 c18_Sm184w1 c18_Sm160 c18_Sm168 c18_Sm48w1 c18_Om128z8 c18_Om80z12 c18_Op0 c18_Op8 c18_Fp24 c18_Fp32 c18_Fp40 c18_Fp48 c18_Fp56 c18_Fp64w1 c18_Fp65w1 c18_Fp16w4 c18_Fp8 c18_Fp0 c18_Om8 c18_Om40 c18_Om48 c18_Om56 c18_Om64 c18_Om68w4 c18_Om16 c18_Om120 c18_Om24 c18_Om32 c18_Om88 c18_Om104 c18_Om112 c18_Om96 ES18 DEF18 DEFref_18 DEFA_18 DEFd3_18 DEFd4_18 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH18 MOK18 MBV18 HQ18 KE.
  pose proof MOK18 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES18 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  set (u18_10 := U R18 10). assert (Wu18_10: 0 <= u18_10 < 2 ^ 64) by (unfold u18_10, U; apply wrange).
  assert (R18_10: getr R18 (reg 10) = Z_to_bv 64 u18_10) by (unfold u18_10, U; symmetry; apply lit_of_word). clearbody u18_10.
  pose proof ES18 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M18 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p2c_conc fx17 R18 M18 (S - 896) (A + 128) u18_10 fb600 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx19 & R19 & M19 & MS19 & K19 & R19_2 & R19_8 & R19_10 & R19_11 & FR19 & GR19).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu18_10. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb600. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF18 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF18); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF18 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF18); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_18 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_18); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_18 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_18); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb600. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c18_Sm600w1 | cellfix c18_Sm600w1]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS19.
  (* [comment removed for export] *)
  assert (AG19: forall a k, ((a + k <= (S - 832) \/ (S - 768) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M18 M19 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR19; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R19_2n: getr R19 (reg 2) = Z_to_bv 64 (S - 768)) by (rewrite R19_2; f_equal; ring). clear R19_2. rename R19_2n into R19_2.
  assert (R19_3: getr R19 (reg 3) = Z_to_bv 64 67584) by (kin K19 3%nat; exact R18_3).
  assert (R19_4: getr R19 (reg 4) = Z_to_bv 64 459832) by (kin K19 4%nat; exact R18_4).
  assert (R19_8n: getr R19 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R19_8; f_equal; ring). clear R19_8. rename R19_8n into R19_8.
  assert (R19_9: getr R19 (reg 9) = Z_to_bv 64 (S + 64)) by (kin K19 9%nat; exact R18_9).
  assert (R19_10n: getr R19 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R19_10; f_equal; ring). clear R19_10. rename R19_10n into R19_10.
  assert (R19_18: getr R19 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K19 18%nat; exact R18_18).
  assert (R19_19: getr R19 (reg 19) = Z_to_bv 64 w872) by (kin K19 19%nat; exact R18_19).
  assert (R19_20: getr R19 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K19 20%nat; exact R18_20).
  assert (c19_Sm472: L5.u64_at RSEGS M19 (S - 472) 142136) by (clear - AG19 c18_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm472]).
  assert (c19_Sm480: L5.u64_at RSEGS M19 (S - 480) (S + 64)) by (clear - AG19 c18_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm480]).
  assert (c19_Sm488: L5.u64_at RSEGS M19 (S - 488) w488) by (clear - AG19 c18_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm488]).
  assert (c19_Sm496: L5.u64_at RSEGS M19 (S - 496) (S + 64)) by (clear - AG19 c18_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm496]).
  assert (c19_Sm504: L5.u64_at RSEGS M19 (S - 504) w504) by (clear - AG19 c18_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm504]).
  assert (c19_Sm512: L5.u64_at RSEGS M19 (S - 512) w512) by (clear - AG19 c18_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm512]).
  assert (c19_Sm520: L5.u64_at RSEGS M19 (S - 520) w520) by (clear - AG19 c18_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm520]).
  assert (c19_Sm528: L5.u64_at RSEGS M19 (S - 528) w528) by (clear - AG19 c18_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm528]).
  assert (c19_Sm536: L5.u64_at RSEGS M19 (S - 536) w536) by (clear - AG19 c18_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm536]).
  assert (c19_Sm544: L5.u64_at RSEGS M19 (S - 544) w544) by (clear - AG19 c18_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm544]).
  assert (c19_Sm552: L5.u64_at RSEGS M19 (S - 552) w552) by (clear - AG19 c18_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm552]).
  assert (c19_Sm560: L5.u64_at RSEGS M19 (S - 560) w560) by (clear - AG19 c18_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm560]).
  assert (c19_Sm568: L5.u64_at RSEGS M19 (S - 568) w568) by (clear - AG19 c18_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm568]).
  assert (c19_Sm424: L5.u64_at RSEGS M19 (S - 424) 141264) by (clear - AG19 c18_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm424]).
  assert (c19_Sm432: L5.u64_at RSEGS M19 (S - 432) (S + 64)) by (clear - AG19 c18_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm432]).
  assert (c19_Sm360: L5.u64_at RSEGS M19 (S - 360) 139904) by (clear - AG19 c18_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm360]).
  assert (c19_Sm368: L5.u64_at RSEGS M19 (S - 368) (S + 64)) by (clear - AG19 c18_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm368]).
  assert (c19_Sm376: L5.u64_at RSEGS M19 (S - 376) (S - 48)) by (clear - AG19 c18_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm376]).
  assert (c19_Sm56: L5.u64_at RSEGS M19 (S - 56) 138528) by (clear - AG19 c18_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm56]).
  assert (c19_Sm64: L5.u64_at RSEGS M19 (S - 64) (S + 64)) by (clear - AG19 c18_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm64]).
  assert (c19_Sm72: L5.u64_at RSEGS M19 (S - 72) (U R0 9)) by (clear - AG19 c18_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm72]).
  assert (c19_Sm80: L5.u64_at RSEGS M19 (S - 80) (U R0 18)) by (clear - AG19 c18_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm80]).
  assert (c19_Sm88: L5.u64_at RSEGS M19 (S - 88) (U R0 19)) by (clear - AG19 c18_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm88]).
  assert (c19_Sm96: L5.u64_at RSEGS M19 (S - 96) (U R0 20)) by (clear - AG19 c18_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm96]).
  assert (c19_Sm104: L5.u64_at RSEGS M19 (S - 104) (U R0 21)) by (clear - AG19 c18_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm104]).
  assert (c19_Sm112: L5.u64_at RSEGS M19 (S - 112) (U R0 22)) by (clear - AG19 c18_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm112]).
  assert (c19_Sm120: L5.u64_at RSEGS M19 (S - 120) (U R0 23)) by (clear - AG19 c18_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm120]).
  assert (c19_Sm128: L5.u64_at RSEGS M19 (S - 128) (U R0 24)) by (clear - AG19 c18_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm128]).
  assert (c19_Sm136: L5.u64_at RSEGS M19 (S - 136) (U R0 25)) by (clear - AG19 c18_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm136]).
  assert (c19_Sm144: L5.u64_at RSEGS M19 (S - 144) (U R0 26)) by (clear - AG19 c18_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm144]).
  assert (c19_Sm152: L5.u64_at RSEGS M19 (S - 152) (U R0 27)) by (clear - AG19 c18_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm152]).
  assert (c19_Sm8: L5.u64_at RSEGS M19 (S - 8) 132608) by (clear - AG19 c18_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm8]).
  assert (c19_Sm16: L5.u64_at RSEGS M19 (S - 16) (U R0 8)) by (clear - AG19 c18_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm16]).
  assert (c19_Sm696w1: L5.u8_at RSEGS M19 (S - 696) fb696) by (clear - AG19 c18_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm696w1]).
  assert (c19_Sm664w1: L5.u8_at RSEGS M19 (S - 664) fb664) by (clear - AG19 c18_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm664w1]).
  assert (c19_Sm640: L5.u64_at RSEGS M19 (S - 640) d1) by (clear - AG19 c18_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm640]).
  assert (c19_Sm648: L5.u64_at RSEGS M19 (S - 648) 8) by (clear - AG19 c18_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm648]).
  assert (c19_Sm632w1: L5.u8_at RSEGS M19 (S - 632) fb632) by (clear - AG19 c18_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm632w1]).
  assert (c19_Sm608: L5.u64_at RSEGS M19 (S - 608) d2) by (clear - AG19 c18_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm608]).
  assert (c19_Sm616: L5.u64_at RSEGS M19 (S - 616) 8) by (clear - AG19 c18_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm616]).
  assert (c19_Sm600w1: L5.u8_at RSEGS M19 (S - 600) fb600) by (clear - AG19 c18_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm600w1]).
  assert (c19_Sm464w1: L5.u8_at RSEGS M19 (S - 464) fb464) by (clear - AG19 c18_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm464w1]).
  assert (c19_Sm408w1: L5.u8_at RSEGS M19 (S - 408) fb408) by (clear - AG19 c18_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm408w1]).
  assert (c19_Sm280w1: L5.u8_at RSEGS M19 (S - 280) fb280) by (clear - AG19 c18_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm280w1]).
  assert (c19_Sm248w1: L5.u8_at RSEGS M19 (S - 248) fb248) by (clear - AG19 c18_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm248w1]).
  assert (c19_Sm216w1: L5.u8_at RSEGS M19 (S - 216) fb216) by (clear - AG19 c18_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm216w1]).
  assert (c19_Sm192: L5.u64_at RSEGS M19 (S - 192) d3) by (clear - AG19 c18_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm192]).
  assert (c19_Sm200: L5.u64_at RSEGS M19 (S - 200) 8) by (clear - AG19 c18_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm200]).
  assert (c19_Sm184w1: L5.u8_at RSEGS M19 (S - 184) fb184) by (clear - AG19 c18_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm184w1]).
  assert (c19_Sm160: L5.u64_at RSEGS M19 (S - 160) d4) by (clear - AG19 c18_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm160]).
  assert (c19_Sm168: L5.u64_at RSEGS M19 (S - 168) 8) by (clear - AG19 c18_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Sm168]).
  assert (c19_Sm48w1: L5.u8_at RSEGS M19 (S - 48) fb48) by (clear - AG19 c18_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Sm48w1]).
  assert (c19_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M19 (A + i) 0)) by (clear - AG19 c18_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | apply c18_Om128z8; exact Hi]).
  assert (c19_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M19 ((A + 48) + i) 0)) by (clear - AG19 c18_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | apply c18_Om80z12; exact Hi]).
  assert (c19_Op0: L5.u64_at RSEGS M19 (A + 128) 373272) by (clear - AG19 c18_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Op0]).
  assert (c19_Op8: L5.u64_at RSEGS M19 (A + 136) (ref + 24)) by (clear - AG19 c18_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Op8]).
  assert (c19_Fp24: L5.u64_at RSEGS M19 (ref + 24) 8028075845441778529) by (clear - AG19 c18_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp24]).
  assert (c19_Fp32: L5.u64_at RSEGS M19 (ref + 32) 7863351059373564014) by (clear - AG19 c18_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp32]).
  assert (c19_Fp40: L5.u64_at RSEGS M19 (ref + 40) 2838809733452757089) by (clear - AG19 c18_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp40]).
  assert (c19_Fp48: L5.u64_at RSEGS M19 (ref + 48) 2334102023183623712) by (clear - AG19 c18_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp48]).
  assert (c19_Fp56: L5.u64_at RSEGS M19 (ref + 56) 4188416081412519009) by (clear - AG19 c18_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp56]).
  assert (c19_Fp64w1: L5.u8_at RSEGS M19 (ref + 64) 48) by (clear - AG19 c18_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Fp64w1]).
  assert (c19_Fp65w1: L5.u8_at RSEGS M19 (ref + 65) 0) by (clear - AG19 c18_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M18 M19 _ _ _ (AG19 _ 1)); [lia | exact c18_Fp65w1]).
  assert (c19_Fp16w4: L5.u32_at RSEGS M19 (ref + 16) 0) by (clear - AG19 c18_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M18 M19 _ _ _ (AG19 _ 4)); [lia | exact c18_Fp16w4]).
  assert (c19_Fp8: L5.u64_at RSEGS M19 (ref + 8) 41) by (clear - AG19 c18_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp8]).
  assert (c19_Fp0: L5.u64_at RSEGS M19 ref 41) by (clear - AG19 c18_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Fp0]).
  assert (c19_Om8: L5.u64_at RSEGS M19 (A + 120) S) by (clear - AG19 c18_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om8]).
  assert (c19_Om40: L5.u64_at RSEGS M19 (A + 88) (A + 128)) by (clear - AG19 c18_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om40]).
  assert (c19_Om48: L5.u64_at RSEGS M19 (A + 80) 133016) by (clear - AG19 c18_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om48]).
  assert (c19_Om56: L5.u64_at RSEGS M19 (A + 72) 91560) by (clear - AG19 c18_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om56]).
  assert (c19_Om64: L5.u64_at RSEGS M19 (A + 64) 91699) by (clear - AG19 c18_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om64]).
  assert (c19_Om68w4: L5.u32_at RSEGS M19 (A + 60) 1) by (clear - AG19 c18_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M18 M19 _ _ _ (AG19 _ 4)); [lia | exact c18_Om68w4]).
  assert (c19_Om16: L5.u64_at RSEGS M19 (A + 112) 0) by (clear - AG19 c18_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om16]).
  assert (c19_Om120: L5.u64_at RSEGS M19 (A + 8) 1) by (clear - AG19 c18_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om120]).
  assert (c19_Om24: L5.u64_at RSEGS M19 (A + 104) 257624) by (clear - AG19 c18_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om24]).
  assert (c19_Om32: L5.u64_at RSEGS M19 (A + 96) 4849336966747728640) by (clear - AG19 c18_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om32]).
  assert (c19_Om88: L5.u64_at RSEGS M19 (A + 40) 142700) by (clear - AG19 c18_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om88]).
  assert (c19_Om104: L5.u64_at RSEGS M19 (A + 24) 253816) by (clear - AG19 c18_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om104]).
  assert (c19_Om112: L5.u64_at RSEGS M19 (A + 16) 373232) by (clear - AG19 c18_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om112]).
  assert (c19_Om96: L5.u64_at RSEGS M19 (A + 32) 142968) by (clear - AG19 c18_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M18 M19 _ _ _ (AG19 _ 8)); [lia | exact c18_Om96]).
  assert (STAT19: forall a, stat_rd av a -> M19 (Z_to_bv 64 a) = M18 (Z_to_bv 64 a)).
  { clear - FR19 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR19; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M18 M19 gd av uid rnd canary hw ES18 STAT19) as ES19.
  assert (DEF19: L5.defined M19 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR19 | exact DEF18]).
  assert (DEFref_19: L5.defined M19 ref 66) by (eapply L5.defined_grows; [exact GR19 | exact DEFref_18]).
  assert (DEFA_19: L5.defined M19 A 144) by (eapply L5.defined_grows; [exact GR19 | exact DEFA_18]).
  assert (DEFd3_19: L5.defined M19 d3 64) by (eapply L5.defined_grows; [exact GR19 | exact DEFd3_18]).
  assert (DEFd4_19: L5.defined M19 d4 64) by (eapply L5.defined_grows; [exact GR19 | exact DEFd4_18]).
  assert (HH19: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M19 (m_vmmaps model18)).
  { clear - HH18 GR19 FR19 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH18. lia. 2: exact GR19. intros a Ha.
    destruct (in_dec (S - 832) (S - 768) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR19; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ19: L5C.hpres L LB1 S 10240 XSF M M19).
  { clear - LBWF HQ18 FR19 GR19 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M18 M19 [((S - 832), 64)]). exact LBWF. lia. exact HQ18.
    { intros x Hx. apply FR19; intros Hin.
        apply (Hx ((S - 832), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR19.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG19 FR19 MS19. try clear STAT19. try clear K18.
  try clear c18_Sm472. try clear c18_Sm480. try clear c18_Sm488. try clear c18_Sm496. try clear c18_Sm504. try clear c18_Sm512. try clear c18_Sm520. try clear c18_Sm528. try clear c18_Sm536. try clear c18_Sm544. try clear c18_Sm552. try clear c18_Sm560. try clear c18_Sm568. try clear c18_Sm424. try clear c18_Sm432. try clear c18_Sm360. try clear c18_Sm368. try clear c18_Sm376. try clear c18_Sm56. try clear c18_Sm64. try clear c18_Sm72. try clear c18_Sm80. try clear c18_Sm88. try clear c18_Sm96. try clear c18_Sm104. try clear c18_Sm112. try clear c18_Sm120. try clear c18_Sm128. try clear c18_Sm136. try clear c18_Sm144. try clear c18_Sm152. try clear c18_Sm8. try clear c18_Sm16. try clear c18_Sm696w1. try clear c18_Sm664w1. try clear c18_Sm640. try clear c18_Sm648. try clear c18_Sm632w1. try clear c18_Sm608. try clear c18_Sm616. try clear c18_Sm600w1. try clear c18_Sm464w1. try clear c18_Sm408w1. try clear c18_Sm280w1. try clear c18_Sm248w1. try clear c18_Sm216w1. try clear c18_Sm192. try clear c18_Sm200. try clear c18_Sm184w1. try clear c18_Sm160. try clear c18_Sm168. try clear c18_Sm48w1. try clear c18_Om128z8. try clear c18_Om80z12. try clear c18_Op0. try clear c18_Op8. try clear c18_Fp24. try clear c18_Fp32. try clear c18_Fp40. try clear c18_Fp48. try clear c18_Fp56. try clear c18_Fp64w1. try clear c18_Fp65w1. try clear c18_Fp16w4. try clear c18_Fp8. try clear c18_Fp0. try clear c18_Om8. try clear c18_Om40. try clear c18_Om48. try clear c18_Om56. try clear c18_Om64. try clear c18_Om68w4. try clear c18_Om16. try clear c18_Om120. try clear c18_Om24. try clear c18_Om32. try clear c18_Om88. try clear c18_Om104. try clear c18_Om112. try clear c18_Om96. try clear R18_2. try clear R18_3. try clear R18_4. try clear R18_8. try clear R18_9. try clear R18_18. try clear R18_19. try clear R18_20. try clear R18_10. try clear DEF18. try clear HH18. try clear HQ18. try clear ES18. try clear DEFref_18. try clear DEFA_18. try clear DEFd3_18. try clear DEFd4_18.
  (* [comment removed for export] *)
  pose proof ES19 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M19 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r2_conc fx19 R19 M19 (S - 896) (A + 128) av canary uid rnd hw w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx20 & R20 & M20 & MS20 & K20 & R20_1 & R20_2 & R20_8 & R20_9 & R20_10 & R20_11 & R20_18 & R20_19 & R20_20 & R20_21 & R20_22 & R20_23 & R20_24 & R20_25 & R20_26 & R20_27 & FR20 & GR20).
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
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww488. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww504. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww512. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww520. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww528. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww536. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww544. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww552. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww560. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww568. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF19 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF19); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF19 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF19); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_19 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_19); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_19 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_19); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c19_Om16 | cellfix c19_Om16]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c19_Om8 | cellfix c19_Om8]. }
  { (* [comment removed for export] *) first [exact c19_Om32 | cellfix c19_Om32]. }
  { (* [comment removed for export] *) first [exact c19_Sm472 | cellfix c19_Sm472]. }
  { (* [comment removed for export] *) first [exact c19_Sm480 | cellfix c19_Sm480]. }
  { (* [comment removed for export] *) first [exact c19_Sm488 | cellfix c19_Sm488]. }
  { (* [comment removed for export] *) first [exact c19_Sm496 | cellfix c19_Sm496]. }
  { (* [comment removed for export] *) first [exact c19_Sm504 | cellfix c19_Sm504]. }
  { (* [comment removed for export] *) first [exact c19_Sm512 | cellfix c19_Sm512]. }
  { (* [comment removed for export] *) first [exact c19_Sm520 | cellfix c19_Sm520]. }
  { (* [comment removed for export] *) first [exact c19_Sm528 | cellfix c19_Sm528]. }
  { (* [comment removed for export] *) first [exact c19_Sm536 | cellfix c19_Sm536]. }
  { (* [comment removed for export] *) first [exact c19_Sm544 | cellfix c19_Sm544]. }
  { (* [comment removed for export] *) first [exact c19_Sm552 | cellfix c19_Sm552]. }
  { (* [comment removed for export] *) first [exact c19_Sm560 | cellfix c19_Sm560]. }
  { (* [comment removed for export] *) first [exact c19_Sm568 | cellfix c19_Sm568]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS20.
  (* [comment removed for export] *)
  assert (AG20: forall a k, ((a + k <= (S - 8832) \/ (S - 768) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M19 M20 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR20; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R20_1n: getr R20 (reg 1) = Z_to_bv 64 142188) by (rewrite R20_1; f_equal; ring). clear R20_1. rename R20_1n into R20_1.
  assert (R20_2n: getr R20 (reg 2) = Z_to_bv 64 (S - 464)) by (rewrite R20_2; f_equal; ring). clear R20_2. rename R20_2n into R20_2.
  assert (R20_3: getr R20 (reg 3) = Z_to_bv 64 67584) by (kin K20 3%nat; exact R19_3).
  assert (R20_4: getr R20 (reg 4) = Z_to_bv 64 459832) by (kin K20 4%nat; exact R19_4).
  assert (R20_8n: getr R20 (reg 8) = Z_to_bv 64 (S + 64)) by (rewrite R20_8; f_equal; ring). clear R20_8. rename R20_8n into R20_8.
  assert (R20_9n: getr R20 (reg 9) = Z_to_bv 64 w488) by (rewrite R20_9; f_equal; ring). clear R20_9. rename R20_9n into R20_9.
  assert (R20_10n: getr R20 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R20_10; f_equal; ring). clear R20_10. rename R20_10n into R20_10.
  assert (R20_11n: getr R20 (reg 11) = Z_to_bv 64 0) by (rewrite R20_11; f_equal; ring). clear R20_11. rename R20_11n into R20_11.
  assert (R20_18n: getr R20 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite R20_18; f_equal; ring). clear R20_18. rename R20_18n into R20_18.
  assert (R20_19n: getr R20 (reg 19) = Z_to_bv 64 w504) by (rewrite R20_19; f_equal; ring). clear R20_19. rename R20_19n into R20_19.
  assert (R20_20n: getr R20 (reg 20) = Z_to_bv 64 w512) by (rewrite R20_20; f_equal; ring). clear R20_20. rename R20_20n into R20_20.
  assert (R20_21n: getr R20 (reg 21) = Z_to_bv 64 w520) by (rewrite R20_21; f_equal; ring). clear R20_21. rename R20_21n into R20_21.
  assert (R20_22n: getr R20 (reg 22) = Z_to_bv 64 w528) by (rewrite R20_22; f_equal; ring). clear R20_22. rename R20_22n into R20_22.
  assert (R20_23n: getr R20 (reg 23) = Z_to_bv 64 w536) by (rewrite R20_23; f_equal; ring). clear R20_23. rename R20_23n into R20_23.
  assert (R20_24n: getr R20 (reg 24) = Z_to_bv 64 w544) by (rewrite R20_24; f_equal; ring). clear R20_24. rename R20_24n into R20_24.
  assert (R20_25n: getr R20 (reg 25) = Z_to_bv 64 w552) by (rewrite R20_25; f_equal; ring). clear R20_25. rename R20_25n into R20_25.
  assert (R20_26n: getr R20 (reg 26) = Z_to_bv 64 w560) by (rewrite R20_26; f_equal; ring). clear R20_26. rename R20_26n into R20_26.
  assert (R20_27n: getr R20 (reg 27) = Z_to_bv 64 w568) by (rewrite R20_27; f_equal; ring). clear R20_27. rename R20_27n into R20_27.
  assert (c20_Sm472: L5.u64_at RSEGS M20 (S - 472) 142136) by (clear - AG20 c19_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm472]).
  assert (c20_Sm480: L5.u64_at RSEGS M20 (S - 480) (S + 64)) by (clear - AG20 c19_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm480]).
  assert (c20_Sm488: L5.u64_at RSEGS M20 (S - 488) w488) by (clear - AG20 c19_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm488]).
  assert (c20_Sm496: L5.u64_at RSEGS M20 (S - 496) (S + 64)) by (clear - AG20 c19_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm496]).
  assert (c20_Sm504: L5.u64_at RSEGS M20 (S - 504) w504) by (clear - AG20 c19_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm504]).
  assert (c20_Sm512: L5.u64_at RSEGS M20 (S - 512) w512) by (clear - AG20 c19_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm512]).
  assert (c20_Sm520: L5.u64_at RSEGS M20 (S - 520) w520) by (clear - AG20 c19_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm520]).
  assert (c20_Sm528: L5.u64_at RSEGS M20 (S - 528) w528) by (clear - AG20 c19_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm528]).
  assert (c20_Sm536: L5.u64_at RSEGS M20 (S - 536) w536) by (clear - AG20 c19_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm536]).
  assert (c20_Sm544: L5.u64_at RSEGS M20 (S - 544) w544) by (clear - AG20 c19_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm544]).
  assert (c20_Sm552: L5.u64_at RSEGS M20 (S - 552) w552) by (clear - AG20 c19_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm552]).
  assert (c20_Sm560: L5.u64_at RSEGS M20 (S - 560) w560) by (clear - AG20 c19_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm560]).
  assert (c20_Sm568: L5.u64_at RSEGS M20 (S - 568) w568) by (clear - AG20 c19_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm568]).
  assert (c20_Sm424: L5.u64_at RSEGS M20 (S - 424) 141264) by (clear - AG20 c19_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm424]).
  assert (c20_Sm432: L5.u64_at RSEGS M20 (S - 432) (S + 64)) by (clear - AG20 c19_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm432]).
  assert (c20_Sm360: L5.u64_at RSEGS M20 (S - 360) 139904) by (clear - AG20 c19_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm360]).
  assert (c20_Sm368: L5.u64_at RSEGS M20 (S - 368) (S + 64)) by (clear - AG20 c19_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm368]).
  assert (c20_Sm376: L5.u64_at RSEGS M20 (S - 376) (S - 48)) by (clear - AG20 c19_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm376]).
  assert (c20_Sm56: L5.u64_at RSEGS M20 (S - 56) 138528) by (clear - AG20 c19_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm56]).
  assert (c20_Sm64: L5.u64_at RSEGS M20 (S - 64) (S + 64)) by (clear - AG20 c19_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm64]).
  assert (c20_Sm72: L5.u64_at RSEGS M20 (S - 72) (U R0 9)) by (clear - AG20 c19_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm72]).
  assert (c20_Sm80: L5.u64_at RSEGS M20 (S - 80) (U R0 18)) by (clear - AG20 c19_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm80]).
  assert (c20_Sm88: L5.u64_at RSEGS M20 (S - 88) (U R0 19)) by (clear - AG20 c19_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm88]).
  assert (c20_Sm96: L5.u64_at RSEGS M20 (S - 96) (U R0 20)) by (clear - AG20 c19_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm96]).
  assert (c20_Sm104: L5.u64_at RSEGS M20 (S - 104) (U R0 21)) by (clear - AG20 c19_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm104]).
  assert (c20_Sm112: L5.u64_at RSEGS M20 (S - 112) (U R0 22)) by (clear - AG20 c19_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm112]).
  assert (c20_Sm120: L5.u64_at RSEGS M20 (S - 120) (U R0 23)) by (clear - AG20 c19_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm120]).
  assert (c20_Sm128: L5.u64_at RSEGS M20 (S - 128) (U R0 24)) by (clear - AG20 c19_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm128]).
  assert (c20_Sm136: L5.u64_at RSEGS M20 (S - 136) (U R0 25)) by (clear - AG20 c19_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm136]).
  assert (c20_Sm144: L5.u64_at RSEGS M20 (S - 144) (U R0 26)) by (clear - AG20 c19_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm144]).
  assert (c20_Sm152: L5.u64_at RSEGS M20 (S - 152) (U R0 27)) by (clear - AG20 c19_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm152]).
  assert (c20_Sm8: L5.u64_at RSEGS M20 (S - 8) 132608) by (clear - AG20 c19_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm8]).
  assert (c20_Sm16: L5.u64_at RSEGS M20 (S - 16) (U R0 8)) by (clear - AG20 c19_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm16]).
  assert (c20_Sm696w1: L5.u8_at RSEGS M20 (S - 696) fb696) by (clear - AG20 c19_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm696w1]).
  assert (c20_Sm664w1: L5.u8_at RSEGS M20 (S - 664) fb664) by (clear - AG20 c19_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm664w1]).
  assert (c20_Sm640: L5.u64_at RSEGS M20 (S - 640) d1) by (clear - AG20 c19_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm640]).
  assert (c20_Sm648: L5.u64_at RSEGS M20 (S - 648) 8) by (clear - AG20 c19_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm648]).
  assert (c20_Sm632w1: L5.u8_at RSEGS M20 (S - 632) fb632) by (clear - AG20 c19_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm632w1]).
  assert (c20_Sm608: L5.u64_at RSEGS M20 (S - 608) d2) by (clear - AG20 c19_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm608]).
  assert (c20_Sm616: L5.u64_at RSEGS M20 (S - 616) 8) by (clear - AG20 c19_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm616]).
  assert (c20_Sm600w1: L5.u8_at RSEGS M20 (S - 600) fb600) by (clear - AG20 c19_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm600w1]).
  assert (c20_Sm464w1: L5.u8_at RSEGS M20 (S - 464) fb464) by (clear - AG20 c19_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm464w1]).
  assert (c20_Sm408w1: L5.u8_at RSEGS M20 (S - 408) fb408) by (clear - AG20 c19_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm408w1]).
  assert (c20_Sm280w1: L5.u8_at RSEGS M20 (S - 280) fb280) by (clear - AG20 c19_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm280w1]).
  assert (c20_Sm248w1: L5.u8_at RSEGS M20 (S - 248) fb248) by (clear - AG20 c19_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm248w1]).
  assert (c20_Sm216w1: L5.u8_at RSEGS M20 (S - 216) fb216) by (clear - AG20 c19_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm216w1]).
  assert (c20_Sm192: L5.u64_at RSEGS M20 (S - 192) d3) by (clear - AG20 c19_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm192]).
  assert (c20_Sm200: L5.u64_at RSEGS M20 (S - 200) 8) by (clear - AG20 c19_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm200]).
  assert (c20_Sm184w1: L5.u8_at RSEGS M20 (S - 184) fb184) by (clear - AG20 c19_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm184w1]).
  assert (c20_Sm160: L5.u64_at RSEGS M20 (S - 160) d4) by (clear - AG20 c19_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm160]).
  assert (c20_Sm168: L5.u64_at RSEGS M20 (S - 168) 8) by (clear - AG20 c19_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Sm168]).
  assert (c20_Sm48w1: L5.u8_at RSEGS M20 (S - 48) fb48) by (clear - AG20 c19_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Sm48w1]).
  assert (c20_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M20 (A + i) 0)) by (clear - AG20 c19_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | apply c19_Om128z8; exact Hi]).
  assert (c20_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M20 ((A + 48) + i) 0)) by (clear - AG20 c19_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | apply c19_Om80z12; exact Hi]).
  assert (c20_Op0: L5.u64_at RSEGS M20 (A + 128) 373272) by (clear - AG20 c19_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Op0]).
  assert (c20_Op8: L5.u64_at RSEGS M20 (A + 136) (ref + 24)) by (clear - AG20 c19_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Op8]).
  assert (c20_Fp24: L5.u64_at RSEGS M20 (ref + 24) 8028075845441778529) by (clear - AG20 c19_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp24]).
  assert (c20_Fp32: L5.u64_at RSEGS M20 (ref + 32) 7863351059373564014) by (clear - AG20 c19_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp32]).
  assert (c20_Fp40: L5.u64_at RSEGS M20 (ref + 40) 2838809733452757089) by (clear - AG20 c19_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp40]).
  assert (c20_Fp48: L5.u64_at RSEGS M20 (ref + 48) 2334102023183623712) by (clear - AG20 c19_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp48]).
  assert (c20_Fp56: L5.u64_at RSEGS M20 (ref + 56) 4188416081412519009) by (clear - AG20 c19_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp56]).
  assert (c20_Fp64w1: L5.u8_at RSEGS M20 (ref + 64) 48) by (clear - AG20 c19_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Fp64w1]).
  assert (c20_Fp65w1: L5.u8_at RSEGS M20 (ref + 65) 0) by (clear - AG20 c19_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M19 M20 _ _ _ (AG20 _ 1)); [lia | exact c19_Fp65w1]).
  assert (c20_Fp16w4: L5.u32_at RSEGS M20 (ref + 16) 0) by (clear - AG20 c19_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M19 M20 _ _ _ (AG20 _ 4)); [lia | exact c19_Fp16w4]).
  assert (c20_Fp8: L5.u64_at RSEGS M20 (ref + 8) 41) by (clear - AG20 c19_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp8]).
  assert (c20_Fp0: L5.u64_at RSEGS M20 ref 41) by (clear - AG20 c19_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Fp0]).
  assert (c20_Om8: L5.u64_at RSEGS M20 (A + 120) S) by (clear - AG20 c19_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om8]).
  assert (c20_Om40: L5.u64_at RSEGS M20 (A + 88) (A + 128)) by (clear - AG20 c19_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om40]).
  assert (c20_Om48: L5.u64_at RSEGS M20 (A + 80) 133016) by (clear - AG20 c19_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om48]).
  assert (c20_Om56: L5.u64_at RSEGS M20 (A + 72) 91560) by (clear - AG20 c19_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om56]).
  assert (c20_Om64: L5.u64_at RSEGS M20 (A + 64) 91699) by (clear - AG20 c19_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om64]).
  assert (c20_Om68w4: L5.u32_at RSEGS M20 (A + 60) 1) by (clear - AG20 c19_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M19 M20 _ _ _ (AG20 _ 4)); [lia | exact c19_Om68w4]).
  assert (c20_Om16: L5.u64_at RSEGS M20 (A + 112) 0) by (clear - AG20 c19_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om16]).
  assert (c20_Om120: L5.u64_at RSEGS M20 (A + 8) 1) by (clear - AG20 c19_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om120]).
  assert (c20_Om24: L5.u64_at RSEGS M20 (A + 104) 257624) by (clear - AG20 c19_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om24]).
  assert (c20_Om32: L5.u64_at RSEGS M20 (A + 96) 4849336966747728640) by (clear - AG20 c19_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om32]).
  assert (c20_Om88: L5.u64_at RSEGS M20 (A + 40) 142700) by (clear - AG20 c19_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om88]).
  assert (c20_Om104: L5.u64_at RSEGS M20 (A + 24) 253816) by (clear - AG20 c19_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om104]).
  assert (c20_Om112: L5.u64_at RSEGS M20 (A + 16) 373232) by (clear - AG20 c19_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om112]).
  assert (c20_Om96: L5.u64_at RSEGS M20 (A + 32) 142968) by (clear - AG20 c19_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M19 M20 _ _ _ (AG20 _ 8)); [lia | exact c19_Om96]).
  assert (STAT20: forall a, stat_rd av a -> M20 (Z_to_bv 64 a) = M19 (Z_to_bv 64 a)).
  { clear - FR20 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR20; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M19 M20 gd av uid rnd canary hw ES19 STAT20) as ES20.
  assert (DEF20: L5.defined M20 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR20 | exact DEF19]).
  assert (DEFref_20: L5.defined M20 ref 66) by (eapply L5.defined_grows; [exact GR20 | exact DEFref_19]).
  assert (DEFA_20: L5.defined M20 A 144) by (eapply L5.defined_grows; [exact GR20 | exact DEFA_19]).
  assert (DEFd3_20: L5.defined M20 d3 64) by (eapply L5.defined_grows; [exact GR20 | exact DEFd3_19]).
  assert (DEFd4_20: L5.defined M20 d4 64) by (eapply L5.defined_grows; [exact GR20 | exact DEFd4_19]).
  assert (HH20: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M20 (m_vmmaps model18)).
  { clear - HH19 GR20 FR20 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH19. lia. 2: exact GR20. intros a Ha.
    destruct (in_dec (S - 8832) (S - 768) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR20; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ20: L5C.hpres L LB1 S 10240 XSF M M20).
  { clear - LBWF HQ19 FR20 GR20 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M19 M20 [((S - 8832), 8064)]). exact LBWF. lia. exact HQ19.
    { intros x Hx. apply FR20; intros Hin.
        apply (Hx ((S - 8832), 8064)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR20.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG20 FR20 MS20. try clear STAT20. try clear K19.
  try clear c19_Sm472. try clear c19_Sm480. try clear c19_Sm488. try clear c19_Sm496. try clear c19_Sm504. try clear c19_Sm512. try clear c19_Sm520. try clear c19_Sm528. try clear c19_Sm536. try clear c19_Sm544. try clear c19_Sm552. try clear c19_Sm560. try clear c19_Sm568. try clear c19_Sm424. try clear c19_Sm432. try clear c19_Sm360. try clear c19_Sm368. try clear c19_Sm376. try clear c19_Sm56. try clear c19_Sm64. try clear c19_Sm72. try clear c19_Sm80. try clear c19_Sm88. try clear c19_Sm96. try clear c19_Sm104. try clear c19_Sm112. try clear c19_Sm120. try clear c19_Sm128. try clear c19_Sm136. try clear c19_Sm144. try clear c19_Sm152. try clear c19_Sm8. try clear c19_Sm16. try clear c19_Sm696w1. try clear c19_Sm664w1. try clear c19_Sm640. try clear c19_Sm648. try clear c19_Sm632w1. try clear c19_Sm608. try clear c19_Sm616. try clear c19_Sm600w1. try clear c19_Sm464w1. try clear c19_Sm408w1. try clear c19_Sm280w1. try clear c19_Sm248w1. try clear c19_Sm216w1. try clear c19_Sm192. try clear c19_Sm200. try clear c19_Sm184w1. try clear c19_Sm160. try clear c19_Sm168. try clear c19_Sm48w1. try clear c19_Om128z8. try clear c19_Om80z12. try clear c19_Op0. try clear c19_Op8. try clear c19_Fp24. try clear c19_Fp32. try clear c19_Fp40. try clear c19_Fp48. try clear c19_Fp56. try clear c19_Fp64w1. try clear c19_Fp65w1. try clear c19_Fp16w4. try clear c19_Fp8. try clear c19_Fp0. try clear c19_Om8. try clear c19_Om40. try clear c19_Om48. try clear c19_Om56. try clear c19_Om64. try clear c19_Om68w4. try clear c19_Om16. try clear c19_Om120. try clear c19_Om24. try clear c19_Om32. try clear c19_Om88. try clear c19_Om104. try clear c19_Om112. try clear c19_Om96. try clear R19_2. try clear R19_3. try clear R19_4. try clear R19_8. try clear R19_9. try clear R19_10. try clear R19_18. try clear R19_19. try clear R19_20. try clear DEF19. try clear HH19. try clear HQ19. try clear ES19. try clear DEFref_19. try clear DEFA_19. try clear DEFd3_19. try clear DEFd4_19.
  eapply (seg12 fx20 R0 R R20 M M20 model model18 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R20_1 R20_2 R20_3 R20_4 R20_8 R20_9 R20_10 R20_11 R20_18 R20_19 R20_20 R20_21 R20_22 R20_23 R20_24 R20_25 R20_26 R20_27 c20_Sm472 c20_Sm480 c20_Sm488 c20_Sm496 c20_Sm504 c20_Sm512 c20_Sm520 c20_Sm528 c20_Sm536 c20_Sm544 c20_Sm552 c20_Sm560 c20_Sm568 c20_Sm424 c20_Sm432 c20_Sm360 c20_Sm368 c20_Sm376 c20_Sm56 c20_Sm64 c20_Sm72 c20_Sm80 c20_Sm88 c20_Sm96 c20_Sm104 c20_Sm112 c20_Sm120 c20_Sm128 c20_Sm136 c20_Sm144 c20_Sm152 c20_Sm8 c20_Sm16 c20_Sm696w1 c20_Sm664w1 c20_Sm640 c20_Sm648 c20_Sm632w1 c20_Sm608 c20_Sm616 c20_Sm600w1 c20_Sm464w1 c20_Sm408w1 c20_Sm280w1 c20_Sm248w1 c20_Sm216w1 c20_Sm192 c20_Sm200 c20_Sm184w1 c20_Sm160 c20_Sm168 c20_Sm48w1 c20_Om128z8 c20_Om80z12 c20_Op0 c20_Op8 c20_Fp24 c20_Fp32 c20_Fp40 c20_Fp48 c20_Fp56 c20_Fp64w1 c20_Fp65w1 c20_Fp16w4 c20_Fp8 c20_Fp0 c20_Om8 c20_Om40 c20_Om48 c20_Om56 c20_Om64 c20_Om68w4 c20_Om16 c20_Om120 c20_Om24 c20_Om32 c20_Om88 c20_Om104 c20_Om112 c20_Om96 ES20 DEF20 DEFref_20 DEFA_20 DEFd3_20 DEFd4_20 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH20 MOK18 MBV18 HQ20 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S11.
