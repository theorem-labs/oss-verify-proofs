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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S9.
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
Let seg10 := L5E3S10.seg10 L HI LY LYX HIok.

Lemma seg9 (fx14 : FPState) (R0 R R14 : bvmap 5 word) (M M14 : word -> option byte) (model model12 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref msg : Z) :
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
  (* [comment removed for export] *) getr R14 (reg 1) = Z_to_bv 64 140248 ->
  (* [comment removed for export] *) getr R14 (reg 2) = Z_to_bv 64 (S - 768) ->
  (* [comment removed for export] *) getr R14 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R14 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R14 (reg 8) = Z_to_bv 64 w784 ->
  (* [comment removed for export] *) getr R14 (reg 9) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R14 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R14 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R14 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R14 (reg 19) = Z_to_bv 64 w872 ->
  (* [comment removed for export] *) getr R14 (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M14 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M14 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 880) msg ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 888) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (S - 896) 49 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M14 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M14 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M14 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M14 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M14 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M14 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M14 ref 66 ->
  (* [comment removed for export] *) L5.defined M14 A 144 ->
  (* [comment removed for export] *) L5.defined M14 d1 64 ->
  (* [comment removed for export] *) L5.defined M14 d2 64 ->
  (* [comment removed for export] *) L5.defined M14 d3 64 ->
  (* [comment removed for export] *) L5.defined M14 d4 64 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d1 64 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d1 \/ d1 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d2 \/ d2 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d3 \/ d3 + 64 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d4 \/ d4 + 64 <= ref) ->
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
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M14 (m_vmmaps model12) ->
  (* [comment removed for export] *) model_ok model12 ->
  (* [comment removed for export] *) model_but_vm model model12 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M14 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx14 R14 140248 M14 model12) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R14_1 R14_2 R14_3 R14_4 R14_8 R14_9 R14_10 R14_11 R14_18 R14_19 R14_20 c14_Sm840 c14_Sm848 c14_Sm856 c14_Sm864 c14_Sm872 c14_Sm776 c14_Sm784 c14_Sm792 c14_Sm800 c14_Sm472 c14_Sm480 c14_Sm488 c14_Sm496 c14_Sm504 c14_Sm512 c14_Sm520 c14_Sm528 c14_Sm536 c14_Sm544 c14_Sm552 c14_Sm560 c14_Sm568 c14_Sm424 c14_Sm432 c14_Sm360 c14_Sm368 c14_Sm376 c14_Sm56 c14_Sm64 c14_Sm72 c14_Sm80 c14_Sm88 c14_Sm96 c14_Sm104 c14_Sm112 c14_Sm120 c14_Sm128 c14_Sm136 c14_Sm144 c14_Sm152 c14_Sm8 c14_Sm16 c14_Sm696w1 c14_Sm664w1 c14_Sm640 c14_Sm648 c14_Sm632w1 c14_Sm608 c14_Sm616 c14_Sm600w1 c14_Sm464w1 c14_Sm408w1 c14_Sm280w1 c14_Sm248w1 c14_Sm216w1 c14_Sm192 c14_Sm200 c14_Sm184w1 c14_Sm160 c14_Sm168 c14_Sm48w1 c14_Om128z8 c14_Om80z12 c14_Sm880 c14_Sm888 c14_Sm896 c14_Op0 c14_Op8 c14_Fp24 c14_Fp32 c14_Fp40 c14_Fp48 c14_Fp56 c14_Fp64w1 c14_Fp65w1 c14_Fp16w4 c14_Fp8 c14_Fp0 c14_Om8 c14_Om40 c14_Om48 c14_Om56 c14_Om64 c14_Om68w4 c14_Om16 c14_Om120 c14_Om24 c14_Om32 c14_Om88 c14_Om104 c14_Om112 c14_Om96 ES14 DEF14 DEFref_14 DEFA_14 DEFd1_14 DEFd2_14 DEFd3_14 DEFd4_14 BR_ref BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH14 MOK12 MBV12 HQ14 KE.
  pose proof MOK12 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES14 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES14 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M14 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p2_conc fx14 R14 M14 (S - 896) (A + 128) fb696 fb664 d1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx15 & R15 & M15 & MS15 & K15 & R15_1 & R15_2 & R15_8 & R15_10 & R15_11 & FR15 & GR15).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb696. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb664. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF14 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF14); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF14 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF14); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_14 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_14); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_14 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_14); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d1 B1_d1 B3_d1 B4_d1 AP_A_d1. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb696. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb664. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c14_Sm696w1 | cellfix c14_Sm696w1]. }
  { (* [comment removed for export] *) rewrite lor1_land254_bit1 by (assumption || kl). first [exact c14_Sm664w1 | cellfix c14_Sm664w1]. }
  { (* [comment removed for export] *) first [exact c14_Sm640 | cellfix c14_Sm640]. }
  { (* [comment removed for export] *) first [exact c14_Sm648 | cellfix c14_Sm648]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS15.
  (* [comment removed for export] *)
  assert (AG15: forall a k, ((a + k <= (S - 832) \/ (S - 768) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M14 M15 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR15; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R15_1n: getr R15 (reg 1) = Z_to_bv 64 140316) by (rewrite R15_1; f_equal; ring). clear R15_1. rename R15_1n into R15_1.
  assert (R15_2n: getr R15 (reg 2) = Z_to_bv 64 (S - 768)) by (rewrite R15_2; f_equal; ring). clear R15_2. rename R15_2n into R15_2.
  assert (R15_3: getr R15 (reg 3) = Z_to_bv 64 67584) by (kin K15 3%nat; exact R14_3).
  assert (R15_4: getr R15 (reg 4) = Z_to_bv 64 459832) by (kin K15 4%nat; exact R14_4).
  assert (R15_8n: getr R15 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R15_8; f_equal; ring). clear R15_8. rename R15_8n into R15_8.
  assert (R15_9: getr R15 (reg 9) = Z_to_bv 64 (S + 64)) by (kin K15 9%nat; exact R14_9).
  assert (R15_10n: getr R15 (reg 10) = Z_to_bv 64 d1) by (rewrite R15_10; f_equal; ring). clear R15_10. rename R15_10n into R15_10.
  assert (R15_11n: getr R15 (reg 11) = Z_to_bv 64 64) by (rewrite R15_11; f_equal; ring). clear R15_11. rename R15_11n into R15_11.
  assert (R15_18: getr R15 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K15 18%nat; exact R14_18).
  assert (R15_19: getr R15 (reg 19) = Z_to_bv 64 w872) by (kin K15 19%nat; exact R14_19).
  assert (R15_20: getr R15 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K15 20%nat; exact R14_20).
  assert (c15_Sm840: L5.u64_at RSEGS M15 (S - 840) 135392) by (clear - AG15 c14_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm840]).
  assert (c15_Sm848: L5.u64_at RSEGS M15 (S - 848) (S + 64)) by (clear - AG15 c14_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm848]).
  assert (c15_Sm856: L5.u64_at RSEGS M15 (S - 856) w856) by (clear - AG15 c14_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm856]).
  assert (c15_Sm864: L5.u64_at RSEGS M15 (S - 864) w864) by (clear - AG15 c14_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm864]).
  assert (c15_Sm872: L5.u64_at RSEGS M15 (S - 872) w872) by (clear - AG15 c14_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm872]).
  assert (c15_Sm472: L5.u64_at RSEGS M15 (S - 472) 142136) by (clear - AG15 c14_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm472]).
  assert (c15_Sm480: L5.u64_at RSEGS M15 (S - 480) (S + 64)) by (clear - AG15 c14_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm480]).
  assert (c15_Sm488: L5.u64_at RSEGS M15 (S - 488) w488) by (clear - AG15 c14_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm488]).
  assert (c15_Sm496: L5.u64_at RSEGS M15 (S - 496) (S + 64)) by (clear - AG15 c14_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm496]).
  assert (c15_Sm504: L5.u64_at RSEGS M15 (S - 504) w504) by (clear - AG15 c14_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm504]).
  assert (c15_Sm512: L5.u64_at RSEGS M15 (S - 512) w512) by (clear - AG15 c14_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm512]).
  assert (c15_Sm520: L5.u64_at RSEGS M15 (S - 520) w520) by (clear - AG15 c14_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm520]).
  assert (c15_Sm528: L5.u64_at RSEGS M15 (S - 528) w528) by (clear - AG15 c14_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm528]).
  assert (c15_Sm536: L5.u64_at RSEGS M15 (S - 536) w536) by (clear - AG15 c14_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm536]).
  assert (c15_Sm544: L5.u64_at RSEGS M15 (S - 544) w544) by (clear - AG15 c14_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm544]).
  assert (c15_Sm552: L5.u64_at RSEGS M15 (S - 552) w552) by (clear - AG15 c14_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm552]).
  assert (c15_Sm560: L5.u64_at RSEGS M15 (S - 560) w560) by (clear - AG15 c14_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm560]).
  assert (c15_Sm568: L5.u64_at RSEGS M15 (S - 568) w568) by (clear - AG15 c14_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm568]).
  assert (c15_Sm424: L5.u64_at RSEGS M15 (S - 424) 141264) by (clear - AG15 c14_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm424]).
  assert (c15_Sm432: L5.u64_at RSEGS M15 (S - 432) (S + 64)) by (clear - AG15 c14_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm432]).
  assert (c15_Sm360: L5.u64_at RSEGS M15 (S - 360) 139904) by (clear - AG15 c14_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm360]).
  assert (c15_Sm368: L5.u64_at RSEGS M15 (S - 368) (S + 64)) by (clear - AG15 c14_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm368]).
  assert (c15_Sm376: L5.u64_at RSEGS M15 (S - 376) (S - 48)) by (clear - AG15 c14_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm376]).
  assert (c15_Sm56: L5.u64_at RSEGS M15 (S - 56) 138528) by (clear - AG15 c14_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm56]).
  assert (c15_Sm64: L5.u64_at RSEGS M15 (S - 64) (S + 64)) by (clear - AG15 c14_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm64]).
  assert (c15_Sm72: L5.u64_at RSEGS M15 (S - 72) (U R0 9)) by (clear - AG15 c14_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm72]).
  assert (c15_Sm80: L5.u64_at RSEGS M15 (S - 80) (U R0 18)) by (clear - AG15 c14_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm80]).
  assert (c15_Sm88: L5.u64_at RSEGS M15 (S - 88) (U R0 19)) by (clear - AG15 c14_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm88]).
  assert (c15_Sm96: L5.u64_at RSEGS M15 (S - 96) (U R0 20)) by (clear - AG15 c14_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm96]).
  assert (c15_Sm104: L5.u64_at RSEGS M15 (S - 104) (U R0 21)) by (clear - AG15 c14_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm104]).
  assert (c15_Sm112: L5.u64_at RSEGS M15 (S - 112) (U R0 22)) by (clear - AG15 c14_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm112]).
  assert (c15_Sm120: L5.u64_at RSEGS M15 (S - 120) (U R0 23)) by (clear - AG15 c14_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm120]).
  assert (c15_Sm128: L5.u64_at RSEGS M15 (S - 128) (U R0 24)) by (clear - AG15 c14_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm128]).
  assert (c15_Sm136: L5.u64_at RSEGS M15 (S - 136) (U R0 25)) by (clear - AG15 c14_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm136]).
  assert (c15_Sm144: L5.u64_at RSEGS M15 (S - 144) (U R0 26)) by (clear - AG15 c14_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm144]).
  assert (c15_Sm152: L5.u64_at RSEGS M15 (S - 152) (U R0 27)) by (clear - AG15 c14_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm152]).
  assert (c15_Sm8: L5.u64_at RSEGS M15 (S - 8) 132608) by (clear - AG15 c14_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm8]).
  assert (c15_Sm16: L5.u64_at RSEGS M15 (S - 16) (U R0 8)) by (clear - AG15 c14_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm16]).
  assert (c15_Sm696w1: L5.u8_at RSEGS M15 (S - 696) fb696) by (clear - AG15 c14_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm696w1]).
  assert (c15_Sm664w1: L5.u8_at RSEGS M15 (S - 664) fb664) by (clear - AG15 c14_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm664w1]).
  assert (c15_Sm640: L5.u64_at RSEGS M15 (S - 640) d1) by (clear - AG15 c14_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm640]).
  assert (c15_Sm648: L5.u64_at RSEGS M15 (S - 648) 8) by (clear - AG15 c14_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm648]).
  assert (c15_Sm632w1: L5.u8_at RSEGS M15 (S - 632) fb632) by (clear - AG15 c14_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm632w1]).
  assert (c15_Sm608: L5.u64_at RSEGS M15 (S - 608) d2) by (clear - AG15 c14_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm608]).
  assert (c15_Sm616: L5.u64_at RSEGS M15 (S - 616) 8) by (clear - AG15 c14_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm616]).
  assert (c15_Sm600w1: L5.u8_at RSEGS M15 (S - 600) fb600) by (clear - AG15 c14_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm600w1]).
  assert (c15_Sm464w1: L5.u8_at RSEGS M15 (S - 464) fb464) by (clear - AG15 c14_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm464w1]).
  assert (c15_Sm408w1: L5.u8_at RSEGS M15 (S - 408) fb408) by (clear - AG15 c14_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm408w1]).
  assert (c15_Sm280w1: L5.u8_at RSEGS M15 (S - 280) fb280) by (clear - AG15 c14_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm280w1]).
  assert (c15_Sm248w1: L5.u8_at RSEGS M15 (S - 248) fb248) by (clear - AG15 c14_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm248w1]).
  assert (c15_Sm216w1: L5.u8_at RSEGS M15 (S - 216) fb216) by (clear - AG15 c14_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm216w1]).
  assert (c15_Sm192: L5.u64_at RSEGS M15 (S - 192) d3) by (clear - AG15 c14_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm192]).
  assert (c15_Sm200: L5.u64_at RSEGS M15 (S - 200) 8) by (clear - AG15 c14_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm200]).
  assert (c15_Sm184w1: L5.u8_at RSEGS M15 (S - 184) fb184) by (clear - AG15 c14_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm184w1]).
  assert (c15_Sm160: L5.u64_at RSEGS M15 (S - 160) d4) by (clear - AG15 c14_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm160]).
  assert (c15_Sm168: L5.u64_at RSEGS M15 (S - 168) 8) by (clear - AG15 c14_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm168]).
  assert (c15_Sm48w1: L5.u8_at RSEGS M15 (S - 48) fb48) by (clear - AG15 c14_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Sm48w1]).
  assert (c15_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M15 (A + i) 0)) by (clear - AG15 c14_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | apply c14_Om128z8; exact Hi]).
  assert (c15_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M15 ((A + 48) + i) 0)) by (clear - AG15 c14_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | apply c14_Om80z12; exact Hi]).
  assert (c15_Sm880: L5.u64_at RSEGS M15 (S - 880) msg) by (clear - AG15 c14_Sm880 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm880]).
  assert (c15_Sm888: L5.u64_at RSEGS M15 (S - 888) 41) by (clear - AG15 c14_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm888]).
  assert (c15_Sm896: L5.u64_at RSEGS M15 (S - 896) 49) by (clear - AG15 c14_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Sm896]).
  assert (c15_Op0: L5.u64_at RSEGS M15 (A + 128) 373272) by (clear - AG15 c14_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Op0]).
  assert (c15_Op8: L5.u64_at RSEGS M15 (A + 136) (ref + 24)) by (clear - AG15 c14_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Op8]).
  assert (c15_Fp24: L5.u64_at RSEGS M15 (ref + 24) 8028075845441778529) by (clear - AG15 c14_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp24]).
  assert (c15_Fp32: L5.u64_at RSEGS M15 (ref + 32) 7863351059373564014) by (clear - AG15 c14_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp32]).
  assert (c15_Fp40: L5.u64_at RSEGS M15 (ref + 40) 2838809733452757089) by (clear - AG15 c14_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp40]).
  assert (c15_Fp48: L5.u64_at RSEGS M15 (ref + 48) 2334102023183623712) by (clear - AG15 c14_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp48]).
  assert (c15_Fp56: L5.u64_at RSEGS M15 (ref + 56) 4188416081412519009) by (clear - AG15 c14_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp56]).
  assert (c15_Fp64w1: L5.u8_at RSEGS M15 (ref + 64) 48) by (clear - AG15 c14_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Fp64w1]).
  assert (c15_Fp65w1: L5.u8_at RSEGS M15 (ref + 65) 0) by (clear - AG15 c14_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M14 M15 _ _ _ (AG15 _ 1)); [lia | exact c14_Fp65w1]).
  assert (c15_Fp16w4: L5.u32_at RSEGS M15 (ref + 16) 0) by (clear - AG15 c14_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M14 M15 _ _ _ (AG15 _ 4)); [lia | exact c14_Fp16w4]).
  assert (c15_Fp8: L5.u64_at RSEGS M15 (ref + 8) 41) by (clear - AG15 c14_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp8]).
  assert (c15_Fp0: L5.u64_at RSEGS M15 ref 41) by (clear - AG15 c14_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Fp0]).
  assert (c15_Om8: L5.u64_at RSEGS M15 (A + 120) S) by (clear - AG15 c14_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om8]).
  assert (c15_Om40: L5.u64_at RSEGS M15 (A + 88) (A + 128)) by (clear - AG15 c14_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om40]).
  assert (c15_Om48: L5.u64_at RSEGS M15 (A + 80) 133016) by (clear - AG15 c14_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om48]).
  assert (c15_Om56: L5.u64_at RSEGS M15 (A + 72) 91560) by (clear - AG15 c14_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om56]).
  assert (c15_Om64: L5.u64_at RSEGS M15 (A + 64) 91699) by (clear - AG15 c14_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om64]).
  assert (c15_Om68w4: L5.u32_at RSEGS M15 (A + 60) 1) by (clear - AG15 c14_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M14 M15 _ _ _ (AG15 _ 4)); [lia | exact c14_Om68w4]).
  assert (c15_Om16: L5.u64_at RSEGS M15 (A + 112) 0) by (clear - AG15 c14_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om16]).
  assert (c15_Om120: L5.u64_at RSEGS M15 (A + 8) 1) by (clear - AG15 c14_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om120]).
  assert (c15_Om24: L5.u64_at RSEGS M15 (A + 104) 257624) by (clear - AG15 c14_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om24]).
  assert (c15_Om32: L5.u64_at RSEGS M15 (A + 96) 4849336966747728640) by (clear - AG15 c14_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om32]).
  assert (c15_Om88: L5.u64_at RSEGS M15 (A + 40) 142700) by (clear - AG15 c14_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om88]).
  assert (c15_Om104: L5.u64_at RSEGS M15 (A + 24) 253816) by (clear - AG15 c14_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om104]).
  assert (c15_Om112: L5.u64_at RSEGS M15 (A + 16) 373232) by (clear - AG15 c14_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om112]).
  assert (c15_Om96: L5.u64_at RSEGS M15 (A + 32) 142968) by (clear - AG15 c14_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M14 M15 _ _ _ (AG15 _ 8)); [lia | exact c14_Om96]).
  assert (STAT15: forall a, stat_rd av a -> M15 (Z_to_bv 64 a) = M14 (Z_to_bv 64 a)).
  { clear - FR15 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR15; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M14 M15 gd av uid rnd canary hw ES14 STAT15) as ES15.
  assert (DEF15: L5.defined M15 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR15 | exact DEF14]).
  assert (DEFref_15: L5.defined M15 ref 66) by (eapply L5.defined_grows; [exact GR15 | exact DEFref_14]).
  assert (DEFA_15: L5.defined M15 A 144) by (eapply L5.defined_grows; [exact GR15 | exact DEFA_14]).
  assert (DEFd1_15: L5.defined M15 d1 64) by (eapply L5.defined_grows; [exact GR15 | exact DEFd1_14]).
  assert (DEFd2_15: L5.defined M15 d2 64) by (eapply L5.defined_grows; [exact GR15 | exact DEFd2_14]).
  assert (DEFd3_15: L5.defined M15 d3 64) by (eapply L5.defined_grows; [exact GR15 | exact DEFd3_14]).
  assert (DEFd4_15: L5.defined M15 d4 64) by (eapply L5.defined_grows; [exact GR15 | exact DEFd4_14]).
  assert (HH15: hi_heap HI ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M15 (m_vmmaps model12)).
  { clear - HH14 GR15 FR15 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH14. lia. 2: exact GR15. intros a Ha.
    destruct (in_dec (S - 832) (S - 768) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR15; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ15: L5C.hpres L LB1 S 10240 XSF M M15).
  { clear - LBWF HQ14 FR15 GR15 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M14 M15 [((S - 832), 64)]). exact LBWF. lia. exact HQ14.
    { intros x Hx. apply FR15; intros Hin.
        apply (Hx ((S - 832), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR15.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG15 FR15 MS15. try clear STAT15. try clear K14.
  try clear c14_Sm840. try clear c14_Sm848. try clear c14_Sm856. try clear c14_Sm864. try clear c14_Sm872. try clear c14_Sm776. try clear c14_Sm784. try clear c14_Sm792. try clear c14_Sm800. try clear c14_Sm472. try clear c14_Sm480. try clear c14_Sm488. try clear c14_Sm496. try clear c14_Sm504. try clear c14_Sm512. try clear c14_Sm520. try clear c14_Sm528. try clear c14_Sm536. try clear c14_Sm544. try clear c14_Sm552. try clear c14_Sm560. try clear c14_Sm568. try clear c14_Sm424. try clear c14_Sm432. try clear c14_Sm360. try clear c14_Sm368. try clear c14_Sm376. try clear c14_Sm56. try clear c14_Sm64. try clear c14_Sm72. try clear c14_Sm80. try clear c14_Sm88. try clear c14_Sm96. try clear c14_Sm104. try clear c14_Sm112. try clear c14_Sm120. try clear c14_Sm128. try clear c14_Sm136. try clear c14_Sm144. try clear c14_Sm152. try clear c14_Sm8. try clear c14_Sm16. try clear c14_Sm696w1. try clear c14_Sm664w1. try clear c14_Sm640. try clear c14_Sm648. try clear c14_Sm632w1. try clear c14_Sm608. try clear c14_Sm616. try clear c14_Sm600w1. try clear c14_Sm464w1. try clear c14_Sm408w1. try clear c14_Sm280w1. try clear c14_Sm248w1. try clear c14_Sm216w1. try clear c14_Sm192. try clear c14_Sm200. try clear c14_Sm184w1. try clear c14_Sm160. try clear c14_Sm168. try clear c14_Sm48w1. try clear c14_Om128z8. try clear c14_Om80z12. try clear c14_Sm880. try clear c14_Sm888. try clear c14_Sm896. try clear c14_Op0. try clear c14_Op8. try clear c14_Fp24. try clear c14_Fp32. try clear c14_Fp40. try clear c14_Fp48. try clear c14_Fp56. try clear c14_Fp64w1. try clear c14_Fp65w1. try clear c14_Fp16w4. try clear c14_Fp8. try clear c14_Fp0. try clear c14_Om8. try clear c14_Om40. try clear c14_Om48. try clear c14_Om56. try clear c14_Om64. try clear c14_Om68w4. try clear c14_Om16. try clear c14_Om120. try clear c14_Om24. try clear c14_Om32. try clear c14_Om88. try clear c14_Om104. try clear c14_Om112. try clear c14_Om96. try clear R14_1. try clear R14_2. try clear R14_3. try clear R14_4. try clear R14_8. try clear R14_9. try clear R14_10. try clear R14_11. try clear R14_18. try clear R14_19. try clear R14_20. try clear DEF14. try clear HH14. try clear HQ14. try clear ES14. try clear DEFref_14. try clear DEFA_14. try clear DEFd1_14. try clear DEFd2_14. try clear DEFd3_14. try clear DEFd4_14.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx15 R15 M15 model12 ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) d1 64 K) as HC.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH15.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - right; right; left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R15_10.
  - rewrite L5CoreKit.L5K.rl4. exact R15_4.
  - rewrite L5CoreKit.L5K.rl1, R15_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R15_2 A16 DEF15 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R15_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-48) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M15 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF15. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R16 M16 model16 RP16 [PRES16 _] MBVn HH16.
    rewrite L5CoreKit.L5K.rl1, R15_1.
    cbn [lb_remove fst app] in PRES16, HH16.
    rewrite (proj2 (Z.eqb_neq ref d1) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref B0_d1 B1_d1 B3_d1 B4_d1 AP_ref_d1)) in PRES16, HH16.
    rewrite (proj2 (Z.eqb_neq A d1) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d1 B1_d1 B3_d1 B4_d1 AP_A_d1)) in PRES16, HH16.
    rewrite Z.eqb_refl in PRES16, HH16.
    rewrite L5CoreKit.L5K.rl2, R15_2, BG.unsigned_lit in PRES16 by (kl SLO SHI STOP).
    match type of PRES16 with heap_pres_core _ _ ?x _ _ => replace x with (S - 768) in PRES16 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 768) M15 M16 PRES16) as HP16. rewrite (ly_stack L LY) in HP16. unfold HEAP_STACK in HP16.
    assert (AGS16: forall a k, ((S - 768) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M15 M16 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP16 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP16. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB16_ref: L5C.agree_on M15 M16 ref 66).
    { clear - HP16 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP16. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB16_A: L5C.agree_on M15 M16 A 144).
    { clear - HP16 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP16. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB16_d2: L5C.agree_on M15 M16 d2 64).
    { clear - HP16 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP16. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d2. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB16_d3: L5C.agree_on M15 M16 d3 64).
    { clear - HP16 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP16. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB16_d4: L5C.agree_on M15 M16 d4 64).
    { clear - HP16 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP16. right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT16: forall a, stat_rd av a -> M16 (Z_to_bv 64 a) = M15 (Z_to_bv 64 a)).
    { clear - HP16 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 768) 8224 [] M15 M16 HP16). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (statics_landed_keep M15 M16 gd av uid rnd canary hw ES15 STAT16) as ES16.
    assert (DEF16: L5.defined M16 (S - 10240) 10240).
    { clear - HP16 DEF15 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 768) 8224 [] M15 M16). exact HP16. lia. lia. lia. lia. exact DEF15. }
    assert (DEFref_16: L5.defined M16 ref 66) by (eapply (L5C.defined_agree M15 M16); [exact AGB16_ref | exact DEFref_15]).
    assert (DEFA_16: L5.defined M16 A 144) by (eapply (L5C.defined_agree M15 M16); [exact AGB16_A | exact DEFA_15]).
    assert (DEFd2_16: L5.defined M16 d2 64) by (eapply (L5C.defined_agree M15 M16); [exact AGB16_d2 | exact DEFd2_15]).
    assert (DEFd3_16: L5.defined M16 d3 64) by (eapply (L5C.defined_agree M15 M16); [exact AGB16_d3 | exact DEFd3_15]).
    assert (DEFd4_16: L5.defined M16 d4 64) by (eapply (L5C.defined_agree M15 M16); [exact AGB16_d4 | exact DEFd4_15]).
    assert (MOK16: model_ok model16).
    { destruct MOK12 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK16 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV12 MBVn) as MBV16. clear MBVn MBV12.
    assert (RPi16: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R16 (reg i) = getr R15 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R15 R16 i RP16). exact Hi. }
    assert (R16_2: getr R16 (reg 2) = Z_to_bv 64 (S - 768)) by (rewrite (RPi16 2%nat) by inl; exact R15_2).
    assert (R16_3: getr R16 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi16 3%nat) by inl; exact R15_3).
    assert (R16_4: getr R16 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi16 4%nat) by inl; exact R15_4).
    assert (R16_8: getr R16 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite (RPi16 8%nat) by inl; exact R15_8).
    assert (R16_9: getr R16 (reg 9) = Z_to_bv 64 (S + 64)) by (rewrite (RPi16 9%nat) by inl; exact R15_9).
    assert (R16_18: getr R16 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite (RPi16 18%nat) by inl; exact R15_18).
    assert (R16_19: getr R16 (reg 19) = Z_to_bv 64 w872) by (rewrite (RPi16 19%nat) by inl; exact R15_19).
    assert (R16_20: getr R16 (reg 20) = Z_to_bv 64 (S - 584)) by (rewrite (RPi16 20%nat) by inl; exact R15_20).
    assert (c16_Sm472: L5.u64_at RSEGS M16 (S - 472) 142136) by (clear - AGS16 c15_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm472]).
    assert (c16_Sm480: L5.u64_at RSEGS M16 (S - 480) (S + 64)) by (clear - AGS16 c15_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm480]).
    assert (c16_Sm488: L5.u64_at RSEGS M16 (S - 488) w488) by (clear - AGS16 c15_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm488]).
    assert (c16_Sm496: L5.u64_at RSEGS M16 (S - 496) (S + 64)) by (clear - AGS16 c15_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm496]).
    assert (c16_Sm504: L5.u64_at RSEGS M16 (S - 504) w504) by (clear - AGS16 c15_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm504]).
    assert (c16_Sm512: L5.u64_at RSEGS M16 (S - 512) w512) by (clear - AGS16 c15_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm512]).
    assert (c16_Sm520: L5.u64_at RSEGS M16 (S - 520) w520) by (clear - AGS16 c15_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm520]).
    assert (c16_Sm528: L5.u64_at RSEGS M16 (S - 528) w528) by (clear - AGS16 c15_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm528]).
    assert (c16_Sm536: L5.u64_at RSEGS M16 (S - 536) w536) by (clear - AGS16 c15_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm536]).
    assert (c16_Sm544: L5.u64_at RSEGS M16 (S - 544) w544) by (clear - AGS16 c15_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm544]).
    assert (c16_Sm552: L5.u64_at RSEGS M16 (S - 552) w552) by (clear - AGS16 c15_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm552]).
    assert (c16_Sm560: L5.u64_at RSEGS M16 (S - 560) w560) by (clear - AGS16 c15_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm560]).
    assert (c16_Sm568: L5.u64_at RSEGS M16 (S - 568) w568) by (clear - AGS16 c15_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm568]).
    assert (c16_Sm424: L5.u64_at RSEGS M16 (S - 424) 141264) by (clear - AGS16 c15_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm424]).
    assert (c16_Sm432: L5.u64_at RSEGS M16 (S - 432) (S + 64)) by (clear - AGS16 c15_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm432]).
    assert (c16_Sm360: L5.u64_at RSEGS M16 (S - 360) 139904) by (clear - AGS16 c15_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm360]).
    assert (c16_Sm368: L5.u64_at RSEGS M16 (S - 368) (S + 64)) by (clear - AGS16 c15_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm368]).
    assert (c16_Sm376: L5.u64_at RSEGS M16 (S - 376) (S - 48)) by (clear - AGS16 c15_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm376]).
    assert (c16_Sm56: L5.u64_at RSEGS M16 (S - 56) 138528) by (clear - AGS16 c15_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm56]).
    assert (c16_Sm64: L5.u64_at RSEGS M16 (S - 64) (S + 64)) by (clear - AGS16 c15_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm64]).
    assert (c16_Sm72: L5.u64_at RSEGS M16 (S - 72) (U R0 9)) by (clear - AGS16 c15_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm72]).
    assert (c16_Sm80: L5.u64_at RSEGS M16 (S - 80) (U R0 18)) by (clear - AGS16 c15_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm80]).
    assert (c16_Sm88: L5.u64_at RSEGS M16 (S - 88) (U R0 19)) by (clear - AGS16 c15_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm88]).
    assert (c16_Sm96: L5.u64_at RSEGS M16 (S - 96) (U R0 20)) by (clear - AGS16 c15_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm96]).
    assert (c16_Sm104: L5.u64_at RSEGS M16 (S - 104) (U R0 21)) by (clear - AGS16 c15_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm104]).
    assert (c16_Sm112: L5.u64_at RSEGS M16 (S - 112) (U R0 22)) by (clear - AGS16 c15_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm112]).
    assert (c16_Sm120: L5.u64_at RSEGS M16 (S - 120) (U R0 23)) by (clear - AGS16 c15_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm120]).
    assert (c16_Sm128: L5.u64_at RSEGS M16 (S - 128) (U R0 24)) by (clear - AGS16 c15_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm128]).
    assert (c16_Sm136: L5.u64_at RSEGS M16 (S - 136) (U R0 25)) by (clear - AGS16 c15_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm136]).
    assert (c16_Sm144: L5.u64_at RSEGS M16 (S - 144) (U R0 26)) by (clear - AGS16 c15_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm144]).
    assert (c16_Sm152: L5.u64_at RSEGS M16 (S - 152) (U R0 27)) by (clear - AGS16 c15_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm152]).
    assert (c16_Sm8: L5.u64_at RSEGS M16 (S - 8) 132608) by (clear - AGS16 c15_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm8]).
    assert (c16_Sm16: L5.u64_at RSEGS M16 (S - 16) (U R0 8)) by (clear - AGS16 c15_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm16]).
    assert (c16_Sm696w1: L5.u8_at RSEGS M16 (S - 696) fb696) by (clear - AGS16 c15_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm696w1]).
    assert (c16_Sm664w1: L5.u8_at RSEGS M16 (S - 664) fb664) by (clear - AGS16 c15_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm664w1]).
    assert (c16_Sm640: L5.u64_at RSEGS M16 (S - 640) d1) by (clear - AGS16 c15_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm640]).
    assert (c16_Sm648: L5.u64_at RSEGS M16 (S - 648) 8) by (clear - AGS16 c15_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm648]).
    assert (c16_Sm632w1: L5.u8_at RSEGS M16 (S - 632) fb632) by (clear - AGS16 c15_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm632w1]).
    assert (c16_Sm608: L5.u64_at RSEGS M16 (S - 608) d2) by (clear - AGS16 c15_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm608]).
    assert (c16_Sm616: L5.u64_at RSEGS M16 (S - 616) 8) by (clear - AGS16 c15_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm616]).
    assert (c16_Sm600w1: L5.u8_at RSEGS M16 (S - 600) fb600) by (clear - AGS16 c15_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm600w1]).
    assert (c16_Sm464w1: L5.u8_at RSEGS M16 (S - 464) fb464) by (clear - AGS16 c15_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm464w1]).
    assert (c16_Sm408w1: L5.u8_at RSEGS M16 (S - 408) fb408) by (clear - AGS16 c15_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm408w1]).
    assert (c16_Sm280w1: L5.u8_at RSEGS M16 (S - 280) fb280) by (clear - AGS16 c15_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm280w1]).
    assert (c16_Sm248w1: L5.u8_at RSEGS M16 (S - 248) fb248) by (clear - AGS16 c15_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm248w1]).
    assert (c16_Sm216w1: L5.u8_at RSEGS M16 (S - 216) fb216) by (clear - AGS16 c15_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm216w1]).
    assert (c16_Sm192: L5.u64_at RSEGS M16 (S - 192) d3) by (clear - AGS16 c15_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm192]).
    assert (c16_Sm200: L5.u64_at RSEGS M16 (S - 200) 8) by (clear - AGS16 c15_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm200]).
    assert (c16_Sm184w1: L5.u8_at RSEGS M16 (S - 184) fb184) by (clear - AGS16 c15_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm184w1]).
    assert (c16_Sm160: L5.u64_at RSEGS M16 (S - 160) d4) by (clear - AGS16 c15_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm160]).
    assert (c16_Sm168: L5.u64_at RSEGS M16 (S - 168) 8) by (clear - AGS16 c15_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M15 M16 _ _ _ (AGS16 _ 8)); [lia | exact c15_Sm168]).
    assert (c16_Sm48w1: L5.u8_at RSEGS M16 (S - 48) fb48) by (clear - AGS16 c15_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M15 M16 _ _ _ (AGS16 _ 1)); [lia | exact c15_Sm48w1]).
    assert (c16_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M16 (A + i) 0)) by (clear - AGB16_A c15_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB16_A); [lia | apply c15_Om128z8; exact Hi]).
    assert (c16_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M16 ((A + 48) + i) 0)) by (clear - AGB16_A c15_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB16_A); [lia | apply c15_Om80z12; exact Hi]).
    assert (c16_Op0: L5.u64_at RSEGS M16 (A + 128) 373272) by (clear - AGB16_A c15_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Op0]).
    assert (c16_Op8: L5.u64_at RSEGS M16 (A + 136) (ref + 24)) by (clear - AGB16_A c15_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Op8]).
    assert (c16_Fp24: L5.u64_at RSEGS M16 (ref + 24) 8028075845441778529) by (clear - AGB16_ref c15_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp24]).
    assert (c16_Fp32: L5.u64_at RSEGS M16 (ref + 32) 7863351059373564014) by (clear - AGB16_ref c15_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp32]).
    assert (c16_Fp40: L5.u64_at RSEGS M16 (ref + 40) 2838809733452757089) by (clear - AGB16_ref c15_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp40]).
    assert (c16_Fp48: L5.u64_at RSEGS M16 (ref + 48) 2334102023183623712) by (clear - AGB16_ref c15_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp48]).
    assert (c16_Fp56: L5.u64_at RSEGS M16 (ref + 56) 4188416081412519009) by (clear - AGB16_ref c15_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp56]).
    assert (c16_Fp64w1: L5.u8_at RSEGS M16 (ref + 64) 48) by (clear - AGB16_ref c15_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp64w1]).
    assert (c16_Fp65w1: L5.u8_at RSEGS M16 (ref + 65) 0) by (clear - AGB16_ref c15_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp65w1]).
    assert (c16_Fp16w4: L5.u32_at RSEGS M16 (ref + 16) 0) by (clear - AGB16_ref c15_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb32 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp16w4]).
    assert (c16_Fp8: L5.u64_at RSEGS M16 (ref + 8) 41) by (clear - AGB16_ref c15_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp8]).
    assert (c16_Fp0: L5.u64_at RSEGS M16 ref 41) by (clear - AGB16_ref c15_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB16_ref); [lia | exact c15_Fp0]).
    assert (c16_Om8: L5.u64_at RSEGS M16 (A + 120) S) by (clear - AGB16_A c15_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om8]).
    assert (c16_Om40: L5.u64_at RSEGS M16 (A + 88) (A + 128)) by (clear - AGB16_A c15_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om40]).
    assert (c16_Om48: L5.u64_at RSEGS M16 (A + 80) 133016) by (clear - AGB16_A c15_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om48]).
    assert (c16_Om56: L5.u64_at RSEGS M16 (A + 72) 91560) by (clear - AGB16_A c15_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om56]).
    assert (c16_Om64: L5.u64_at RSEGS M16 (A + 64) 91699) by (clear - AGB16_A c15_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om64]).
    assert (c16_Om68w4: L5.u32_at RSEGS M16 (A + 60) 1) by (clear - AGB16_A c15_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb32 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om68w4]).
    assert (c16_Om16: L5.u64_at RSEGS M16 (A + 112) 0) by (clear - AGB16_A c15_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om16]).
    assert (c16_Om120: L5.u64_at RSEGS M16 (A + 8) 1) by (clear - AGB16_A c15_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om120]).
    assert (c16_Om24: L5.u64_at RSEGS M16 (A + 104) 257624) by (clear - AGB16_A c15_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om24]).
    assert (c16_Om32: L5.u64_at RSEGS M16 (A + 96) 4849336966747728640) by (clear - AGB16_A c15_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om32]).
    assert (c16_Om88: L5.u64_at RSEGS M16 (A + 40) 142700) by (clear - AGB16_A c15_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om88]).
    assert (c16_Om104: L5.u64_at RSEGS M16 (A + 24) 253816) by (clear - AGB16_A c15_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om104]).
    assert (c16_Om112: L5.u64_at RSEGS M16 (A + 16) 373232) by (clear - AGB16_A c15_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om112]).
    assert (c16_Om96: L5.u64_at RSEGS M16 (A + 32) 142968) by (clear - AGB16_A c15_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB16_A); [lia | exact c15_Om96]).
    assert (HQ16: L5C.hpres L LB1 S 10240 XSF M M16).
    { clear - LBWF HQ15 HP16 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((ref, 66) :: (A, 144) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 768) 8224 [] M M15 M16). exact LBWF. lia. lia. exact HQ15. exact HP16. intros bb Hbb; right; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS16 STAT16 PRES16 RP16 RPi16 HP16 AGB16_ref AGB16_A AGB16_d2 AGB16_d3 AGB16_d4.
    try clear c15_Sm840 c15_Sm848 c15_Sm856 c15_Sm864 c15_Sm872 c15_Sm472 c15_Sm480 c15_Sm488 c15_Sm496 c15_Sm504 c15_Sm512 c15_Sm520 c15_Sm528 c15_Sm536 c15_Sm544 c15_Sm552 c15_Sm560 c15_Sm568 c15_Sm424 c15_Sm432 c15_Sm360 c15_Sm368 c15_Sm376 c15_Sm56 c15_Sm64 c15_Sm72 c15_Sm80 c15_Sm88 c15_Sm96 c15_Sm104 c15_Sm112 c15_Sm120 c15_Sm128 c15_Sm136 c15_Sm144 c15_Sm152 c15_Sm8 c15_Sm16 c15_Sm696w1 c15_Sm664w1 c15_Sm640 c15_Sm648 c15_Sm632w1 c15_Sm608 c15_Sm616 c15_Sm600w1 c15_Sm464w1 c15_Sm408w1 c15_Sm280w1 c15_Sm248w1 c15_Sm216w1 c15_Sm192 c15_Sm200 c15_Sm184w1 c15_Sm160 c15_Sm168 c15_Sm48w1 c15_Om128z8 c15_Om80z12 c15_Sm880 c15_Sm888 c15_Sm896 c15_Op0 c15_Op8 c15_Fp24 c15_Fp32 c15_Fp40 c15_Fp48 c15_Fp56 c15_Fp64w1 c15_Fp65w1 c15_Fp16w4 c15_Fp8 c15_Fp0 c15_Om8 c15_Om40 c15_Om48 c15_Om56 c15_Om64 c15_Om68w4 c15_Om16 c15_Om120 c15_Om24 c15_Om32 c15_Om88 c15_Om104 c15_Om112 c15_Om96 R15_1 R15_2 R15_3 R15_4 R15_8 R15_9 R15_10 R15_11 R15_18 R15_19 R15_20 DEF15 HH15 HQ15 ES15 K15 DEFref_15 DEFA_15 DEFd1_15 DEFd2_15 DEFd3_15 DEFd4_15.
    eapply (seg10 fx15 R0 R R16 M M16 model model16 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R16_2 R16_3 R16_4 R16_8 R16_9 R16_18 R16_19 R16_20 c16_Sm472 c16_Sm480 c16_Sm488 c16_Sm496 c16_Sm504 c16_Sm512 c16_Sm520 c16_Sm528 c16_Sm536 c16_Sm544 c16_Sm552 c16_Sm560 c16_Sm568 c16_Sm424 c16_Sm432 c16_Sm360 c16_Sm368 c16_Sm376 c16_Sm56 c16_Sm64 c16_Sm72 c16_Sm80 c16_Sm88 c16_Sm96 c16_Sm104 c16_Sm112 c16_Sm120 c16_Sm128 c16_Sm136 c16_Sm144 c16_Sm152 c16_Sm8 c16_Sm16 c16_Sm696w1 c16_Sm664w1 c16_Sm640 c16_Sm648 c16_Sm632w1 c16_Sm608 c16_Sm616 c16_Sm600w1 c16_Sm464w1 c16_Sm408w1 c16_Sm280w1 c16_Sm248w1 c16_Sm216w1 c16_Sm192 c16_Sm200 c16_Sm184w1 c16_Sm160 c16_Sm168 c16_Sm48w1 c16_Om128z8 c16_Om80z12 c16_Op0 c16_Op8 c16_Fp24 c16_Fp32 c16_Fp40 c16_Fp48 c16_Fp56 c16_Fp64w1 c16_Fp65w1 c16_Fp16w4 c16_Fp8 c16_Fp0 c16_Om8 c16_Om40 c16_Om48 c16_Om56 c16_Om64 c16_Om68w4 c16_Om16 c16_Om120 c16_Om24 c16_Om32 c16_Om88 c16_Om104 c16_Om112 c16_Om96 ES16 DEF16 DEFref_16 DEFA_16 DEFd2_16 DEFd3_16 DEFd4_16 BR_ref BR_A BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d2 AP_A_d3 AP_A_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH16 MOK16 MBV16 HQ16 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S9.
