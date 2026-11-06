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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S4.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S3.
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
Let seg4 := L5E3S4.seg4 L HI LY LYX HIok.

Lemma seg3 (fx4 : FPState) (R0 R R5 : bvmap 5 word) (M M5 : word -> option byte) (model model5 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A msg u0_9 u3_19 u3_18 : Z) :
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
  (* [comment removed for export] *) getr R5 (reg 2) = Z_to_bv 64 (S - 960) ->
  (* [comment removed for export] *) getr R5 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R5 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R5 (reg 8) = Z_to_bv 64 48 ->
  (* [comment removed for export] *) getr R5 (reg 9) = Z_to_bv 64 41 ->
  (* [comment removed for export] *) getr R5 (reg 10) = Z_to_bv 64 msg ->
  (* [comment removed for export] *) getr R5 (reg 18) = Z_to_bv 64 (S - 896) ->
  (* [comment removed for export] *) getr R5 (reg 19) = Z_to_bv 64 u3_19 ->
  (* [comment removed for export] *) getr R5 (reg 20) = Z_to_bv 64 48 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M5 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M5 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M5 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 960) 74669 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 952) 136012 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 944) (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 936) u3_19 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 928) u3_18 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 920) u0_9 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 912) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M5 (S - 904) 136328 ->
  (* [comment removed for export] *) e1_statics M5 gd fl av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M5 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M5 msg 48 ->
  (* [comment removed for export] *) L5.defined M5 A 144 ->
  (* [comment removed for export] *) L5.defined M5 d1 64 ->
  (* [comment removed for export] *) L5.defined M5 d2 64 ->
  (* [comment removed for export] *) L5.defined M5 d3 64 ->
  (* [comment removed for export] *) L5.defined M5 d4 64 ->
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
  (* [comment removed for export] *) hi_heap HI ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (cr) 144) 48) M5 (m_vmmaps model5) ->
  (* [comment removed for export] *) model_ok model5 ->
  (* [comment removed for export] *) model_but_vm model model5 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M5 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx4 R5 368844 M5 model5) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 Wu3_19 Wu3_18 R5_2 R5_3 R5_4 R5_8 R5_9 R5_10 R5_18 R5_19 R5_20 c5_Sm840 c5_Sm848 c5_Sm856 c5_Sm864 c5_Sm872 c5_Sm776 c5_Sm784 c5_Sm792 c5_Sm800 c5_Sm472 c5_Sm480 c5_Sm488 c5_Sm496 c5_Sm504 c5_Sm512 c5_Sm520 c5_Sm528 c5_Sm536 c5_Sm544 c5_Sm552 c5_Sm560 c5_Sm568 c5_Sm424 c5_Sm432 c5_Sm360 c5_Sm368 c5_Sm376 c5_Sm56 c5_Sm64 c5_Sm72 c5_Sm80 c5_Sm88 c5_Sm96 c5_Sm104 c5_Sm112 c5_Sm120 c5_Sm128 c5_Sm136 c5_Sm144 c5_Sm152 c5_Sm8 c5_Sm16 c5_Sm696w1 c5_Sm664w1 c5_Sm640 c5_Sm648 c5_Sm632w1 c5_Sm608 c5_Sm616 c5_Sm600w1 c5_Sm464w1 c5_Sm408w1 c5_Sm280w1 c5_Sm248w1 c5_Sm216w1 c5_Sm192 c5_Sm200 c5_Sm184w1 c5_Sm160 c5_Sm168 c5_Sm48w1 c5_Om128z8 c5_Om80z12 c5_Sm960 c5_Sm952 c5_Sm944 c5_Sm936 c5_Sm928 c5_Sm920 c5_Sm912 c5_Sm904 ES5 DEF5 DEFmsg_5 DEFA_5 DEFd1_5 DEFd2_5 DEFd3_5 DEFd4_5 BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_msg FRSH_A HH5 MOK5 MBV5 HQ5 KE.
  pose proof MOK5 as (Mh & Ml & Mm).
  pose proof BR_msg as (B0_msg & B1_msg & B2_msg & B3_msg & B4_msg). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_msg. unfold hl_ceil in B4_msg.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES5 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9.
  pose proof (auxv_cells M5 av uid rnd hw S_13) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  assert (WUW: L5.writable RSEGS M5 459617 6). { apply (writable_img M5 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; kl. }
  assert (WUC: L5.writable RSEGS M5 456960 4). { apply (writable_img M5 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; kl. }
  assert (STEP6: exists (fx6 : FPState) (R6 : bvmap 5 word) (M6 : word -> option byte),
       msteps RSEGS (st fx4 R5 368844 M5) (st fx6 R6 136108 M6)
    /\ (forall i, In i [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R6 (reg i) = getr R5 (reg i))
    /\ getr R6 (reg 1) = Z_to_bv 64 (136340)
    /\ getr R6 (reg 2) = Z_to_bv 64 ((S - 896) - 16)
    /\ getr R6 (reg 8) = Z_to_bv 64 ((A + 128))
    /\ getr R6 (reg 9) = Z_to_bv 64 (u0_9)
    /\ getr R6 (reg 10) = Z_to_bv 64 ((A + 128))
    /\ getr R6 (reg 11) = Z_to_bv 64 ((S - 896))
    /\ getr R6 (reg 18) = Z_to_bv 64 (u3_18)
    /\ getr R6 (reg 19) = Z_to_bv 64 (u3_19)
    /\ getr R6 (reg 20) = Z_to_bv 64 ((S - 896) + 312)
    /\ L5.u64_at RSEGS M6 (((S - 896)) - 16) ((A + 128))
    /\ L5.u64_at RSEGS M6 (((S - 896)) - 8) (136340)
    /\ L5.u8_at RSEGS M6 ((msg) + 41) (0)
    /\ L5.u64_at RSEGS M6 ((msg) + 0) (8028075845441778529)
    /\ L5.u64_at RSEGS M6 ((msg) + 8) (7863351059373564014)
    /\ L5.u64_at RSEGS M6 ((msg) + 16) (2838809733452757089)
    /\ L5.u64_at RSEGS M6 ((msg) + 24) (2334102023183623712)
    /\ L5.u64_at RSEGS M6 ((msg) + 32) (4188416081412519009)
    /\ L5.u8_at RSEGS M6 ((msg) + 40) (48)
    /\ L5.u64_at RSEGS M6 (((S - 896)) + 16) (msg)
    /\ L5.u64_at RSEGS M6 (((S - 896)) + 8) (41)
    /\ L5.u64_at RSEGS M6 (((S - 896)) + 0) (49)
    /\ (forall x : word, ~ (((S - 896)) + -128 <= bv_unsigned x < ((S - 896)) + -128 + (64)) -> ~ (((S - 896)) + -16 <= bv_unsigned x < ((S - 896)) + -16 + (8)) -> ~ (((S - 896)) + -8 <= bv_unsigned x < ((S - 896)) + -8 + (8)) -> ~ (((S - 896)) + 0 <= bv_unsigned x < ((S - 896)) + 0 + (8)) -> ~ (((S - 896)) + 8 <= bv_unsigned x < ((S - 896)) + 8 + (8)) -> ~ (((S - 896)) + 16 <= bv_unsigned x < ((S - 896)) + 16 + (8)) -> ~ ((msg) + 0 <= bv_unsigned x < (msg) + 0 + (42)) -> M6 x = M5 x)
    /\ mem_grows M5 M6).
  { pose proof B1_msg as Bsplit. destruct Bsplit as [BLO|BHI].
    - idtac.
      unshelve epose proof (e3s2_bl_conc fx4 R5 M5 (S - 896) (A + 128) msg u0_9 u3_18 u3_19 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        as (fxv & Rv & Mv & MSv & Kv & REST).
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu0_9. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_18. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_19. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF5); lia. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEFA_5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEFA_5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_5); lia. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEFmsg_5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFmsg_5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEFmsg_5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. apply (L5.defined_sub _ _ _ _ _ DEFmsg_5); lia. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) first [exact c5_Sm952 | cellfix c5_Sm952]. }
      { (* [comment removed for export] *) first [exact c5_Sm960 | cellfix c5_Sm960]. }
      { (* [comment removed for export] *) first [exact c5_Sm904 | cellfix c5_Sm904]. }
      { (* [comment removed for export] *) first [exact c5_Sm912 | cellfix c5_Sm912]. }
      { (* [comment removed for export] *) first [exact c5_Sm920 | cellfix c5_Sm920]. }
      { (* [comment removed for export] *) first [exact c5_Sm928 | cellfix c5_Sm928]. }
      { (* [comment removed for export] *) first [exact c5_Sm936 | cellfix c5_Sm936]. }
      { (* [comment removed for export] *) first [exact c5_Sm944 | cellfix c5_Sm944]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BLO LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      exists fxv, Rv, Mv. split. exact MSv.
      split. { intros i Hi. apply Kv. apply L5KP.In_of_existsb. revert Hi; clear; intros Hi. cbn in Hi. decompose [or] Hi; subst; try reflexivity; contradiction. }
      decompose [and] REST; repeat split; assumption.
    - idtac.
      unshelve epose proof (e3s2_bh_conc fx4 R5 M5 (S - 896) (A + 128) msg u0_9 u3_18 u3_19 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        as (fxv & Rv & Mv & MSv & Kv & REST).
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu0_9. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_18. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_19. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF5); lia. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEFA_5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEFA_5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_5); lia. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) clear - DEFmsg_5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFmsg_5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEFmsg_5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. apply (L5.defined_sub _ _ _ _ _ DEFmsg_5); lia. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
      { (* [comment removed for export] *) kl BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) pr. }
      { (* [comment removed for export] *) first [exact c5_Sm952 | cellfix c5_Sm952]. }
      { (* [comment removed for export] *) first [exact c5_Sm960 | cellfix c5_Sm960]. }
      { (* [comment removed for export] *) first [exact c5_Sm904 | cellfix c5_Sm904]. }
      { (* [comment removed for export] *) first [exact c5_Sm912 | cellfix c5_Sm912]. }
      { (* [comment removed for export] *) first [exact c5_Sm920 | cellfix c5_Sm920]. }
      { (* [comment removed for export] *) first [exact c5_Sm928 | cellfix c5_Sm928]. }
      { (* [comment removed for export] *) first [exact c5_Sm936 | cellfix c5_Sm936]. }
      { (* [comment removed for export] *) first [exact c5_Sm944 | cellfix c5_Sm944]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      { (* [comment removed for export] *) clear - DEF5 BHI LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF5); lia | lia | lia]. }
      exists fxv, Rv, Mv. split. exact MSv.
      split. { intros i Hi. apply Kv. apply L5KP.In_of_existsb. revert Hi; clear; intros Hi. cbn in Hi. decompose [or] Hi; subst; try reflexivity; contradiction. }
      decompose [and] REST; repeat split; assumption.
  }
  try clear U_0 U_1 U_2 U_3 U_4 U_5.
  destruct STEP6 as (fx6 & R6 & M6 & MS6 & K6 & R6_1 & R6_2 & R6_8 & R6_9 & R6_10 & R6_11 & R6_18 & R6_19 & R6_20 & C6_0 & C6_1 & C6_2 & C6_3 & C6_4 & C6_5 & C6_6 & C6_7 & C6_8 & C6_9 & C6_10 & C6_11 & FR6 & GR6).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS6.
  (* [comment removed for export] *)
  assert (AG6: forall a k, ((a + k <= (S - 1024) \/ (S - 960) <= a) /\ (a + k <= (S - 912) \/ (S - 904) <= a) /\ (a + k <= (S - 904) \/ (S - 896) <= a) /\ (a + k <= (S - 896) \/ (S - 888) <= a) /\ (a + k <= (S - 888) \/ (S - 880) <= a) /\ (a + k <= (S - 880) \/ (S - 872) <= a) /\ (a + k <= msg \/ (msg + 42) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M5 M6 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & E1 & E2 & E3 & E4 & E5 & E6 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR6; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E1 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E2 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E3 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E4 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E5 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E6 Hi; lia]. }
  assert (R6_1n: getr R6 (reg 1) = Z_to_bv 64 136340) by (rewrite R6_1; f_equal; ring). clear R6_1. rename R6_1n into R6_1.
  assert (R6_2n: getr R6 (reg 2) = Z_to_bv 64 (S - 912)) by (rewrite R6_2; f_equal; ring). clear R6_2. rename R6_2n into R6_2.
  assert (R6_3: getr R6 (reg 3) = Z_to_bv 64 67584) by (kin K6 3%nat; exact R5_3).
  assert (R6_4: getr R6 (reg 4) = Z_to_bv 64 459832) by (kin K6 4%nat; exact R5_4).
  assert (R6_8n: getr R6 (reg 8) = Z_to_bv 64 (A + 128)) by (rewrite R6_8; f_equal; ring). clear R6_8. rename R6_8n into R6_8.
  assert (R6_9n: getr R6 (reg 9) = Z_to_bv 64 u0_9) by (rewrite R6_9; f_equal; ring). clear R6_9. rename R6_9n into R6_9.
  assert (R6_10n: getr R6 (reg 10) = Z_to_bv 64 (A + 128)) by (rewrite R6_10; f_equal; ring). clear R6_10. rename R6_10n into R6_10.
  assert (R6_11n: getr R6 (reg 11) = Z_to_bv 64 (S - 896)) by (rewrite R6_11; f_equal; ring). clear R6_11. rename R6_11n into R6_11.
  assert (R6_18n: getr R6 (reg 18) = Z_to_bv 64 u3_18) by (rewrite R6_18; f_equal; ring). clear R6_18. rename R6_18n into R6_18.
  assert (R6_19n: getr R6 (reg 19) = Z_to_bv 64 u3_19) by (rewrite R6_19; f_equal; ring). clear R6_19. rename R6_19n into R6_19.
  assert (R6_20n: getr R6 (reg 20) = Z_to_bv 64 (S - 584)) by (rewrite R6_20; f_equal; ring). clear R6_20. rename R6_20n into R6_20.
  assert (c6_Sm840: L5.u64_at RSEGS M6 (S - 840) 135392) by (clear - AG6 c5_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm840]).
  assert (c6_Sm848: L5.u64_at RSEGS M6 (S - 848) (S + 64)) by (clear - AG6 c5_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm848]).
  assert (c6_Sm856: L5.u64_at RSEGS M6 (S - 856) w856) by (clear - AG6 c5_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm856]).
  assert (c6_Sm864: L5.u64_at RSEGS M6 (S - 864) w864) by (clear - AG6 c5_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm864]).
  assert (c6_Sm872: L5.u64_at RSEGS M6 (S - 872) w872) by (clear - AG6 c5_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm872]).
  assert (c6_Sm776: L5.u64_at RSEGS M6 (S - 776) 139520) by (clear - AG6 c5_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm776]).
  assert (c6_Sm784: L5.u64_at RSEGS M6 (S - 784) w784) by (clear - AG6 c5_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm784]).
  assert (c6_Sm792: L5.u64_at RSEGS M6 (S - 792) (S + 64)) by (clear - AG6 c5_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm792]).
  assert (c6_Sm800: L5.u64_at RSEGS M6 (S - 800) (S + 64)) by (clear - AG6 c5_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm800]).
  assert (c6_Sm472: L5.u64_at RSEGS M6 (S - 472) 142136) by (clear - AG6 c5_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm472]).
  assert (c6_Sm480: L5.u64_at RSEGS M6 (S - 480) (S + 64)) by (clear - AG6 c5_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm480]).
  assert (c6_Sm488: L5.u64_at RSEGS M6 (S - 488) w488) by (clear - AG6 c5_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm488]).
  assert (c6_Sm496: L5.u64_at RSEGS M6 (S - 496) (S + 64)) by (clear - AG6 c5_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm496]).
  assert (c6_Sm504: L5.u64_at RSEGS M6 (S - 504) w504) by (clear - AG6 c5_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm504]).
  assert (c6_Sm512: L5.u64_at RSEGS M6 (S - 512) w512) by (clear - AG6 c5_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm512]).
  assert (c6_Sm520: L5.u64_at RSEGS M6 (S - 520) w520) by (clear - AG6 c5_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm520]).
  assert (c6_Sm528: L5.u64_at RSEGS M6 (S - 528) w528) by (clear - AG6 c5_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm528]).
  assert (c6_Sm536: L5.u64_at RSEGS M6 (S - 536) w536) by (clear - AG6 c5_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm536]).
  assert (c6_Sm544: L5.u64_at RSEGS M6 (S - 544) w544) by (clear - AG6 c5_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm544]).
  assert (c6_Sm552: L5.u64_at RSEGS M6 (S - 552) w552) by (clear - AG6 c5_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm552]).
  assert (c6_Sm560: L5.u64_at RSEGS M6 (S - 560) w560) by (clear - AG6 c5_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm560]).
  assert (c6_Sm568: L5.u64_at RSEGS M6 (S - 568) w568) by (clear - AG6 c5_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm568]).
  assert (c6_Sm424: L5.u64_at RSEGS M6 (S - 424) 141264) by (clear - AG6 c5_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm424]).
  assert (c6_Sm432: L5.u64_at RSEGS M6 (S - 432) (S + 64)) by (clear - AG6 c5_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm432]).
  assert (c6_Sm360: L5.u64_at RSEGS M6 (S - 360) 139904) by (clear - AG6 c5_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm360]).
  assert (c6_Sm368: L5.u64_at RSEGS M6 (S - 368) (S + 64)) by (clear - AG6 c5_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm368]).
  assert (c6_Sm376: L5.u64_at RSEGS M6 (S - 376) (S - 48)) by (clear - AG6 c5_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm376]).
  assert (c6_Sm56: L5.u64_at RSEGS M6 (S - 56) 138528) by (clear - AG6 c5_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm56]).
  assert (c6_Sm64: L5.u64_at RSEGS M6 (S - 64) (S + 64)) by (clear - AG6 c5_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm64]).
  assert (c6_Sm72: L5.u64_at RSEGS M6 (S - 72) (U R0 9)) by (clear - AG6 c5_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm72]).
  assert (c6_Sm80: L5.u64_at RSEGS M6 (S - 80) (U R0 18)) by (clear - AG6 c5_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm80]).
  assert (c6_Sm88: L5.u64_at RSEGS M6 (S - 88) (U R0 19)) by (clear - AG6 c5_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm88]).
  assert (c6_Sm96: L5.u64_at RSEGS M6 (S - 96) (U R0 20)) by (clear - AG6 c5_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm96]).
  assert (c6_Sm104: L5.u64_at RSEGS M6 (S - 104) (U R0 21)) by (clear - AG6 c5_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm104]).
  assert (c6_Sm112: L5.u64_at RSEGS M6 (S - 112) (U R0 22)) by (clear - AG6 c5_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm112]).
  assert (c6_Sm120: L5.u64_at RSEGS M6 (S - 120) (U R0 23)) by (clear - AG6 c5_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm120]).
  assert (c6_Sm128: L5.u64_at RSEGS M6 (S - 128) (U R0 24)) by (clear - AG6 c5_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm128]).
  assert (c6_Sm136: L5.u64_at RSEGS M6 (S - 136) (U R0 25)) by (clear - AG6 c5_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm136]).
  assert (c6_Sm144: L5.u64_at RSEGS M6 (S - 144) (U R0 26)) by (clear - AG6 c5_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm144]).
  assert (c6_Sm152: L5.u64_at RSEGS M6 (S - 152) (U R0 27)) by (clear - AG6 c5_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm152]).
  assert (c6_Sm8: L5.u64_at RSEGS M6 (S - 8) 132608) by (clear - AG6 c5_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm8]).
  assert (c6_Sm16: L5.u64_at RSEGS M6 (S - 16) (U R0 8)) by (clear - AG6 c5_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm16]).
  assert (c6_Sm696w1: L5.u8_at RSEGS M6 (S - 696) fb696) by (clear - AG6 c5_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm696w1]).
  assert (c6_Sm664w1: L5.u8_at RSEGS M6 (S - 664) fb664) by (clear - AG6 c5_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm664w1]).
  assert (c6_Sm640: L5.u64_at RSEGS M6 (S - 640) d1) by (clear - AG6 c5_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm640]).
  assert (c6_Sm648: L5.u64_at RSEGS M6 (S - 648) 8) by (clear - AG6 c5_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm648]).
  assert (c6_Sm632w1: L5.u8_at RSEGS M6 (S - 632) fb632) by (clear - AG6 c5_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm632w1]).
  assert (c6_Sm608: L5.u64_at RSEGS M6 (S - 608) d2) by (clear - AG6 c5_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm608]).
  assert (c6_Sm616: L5.u64_at RSEGS M6 (S - 616) 8) by (clear - AG6 c5_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm616]).
  assert (c6_Sm600w1: L5.u8_at RSEGS M6 (S - 600) fb600) by (clear - AG6 c5_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm600w1]).
  assert (c6_Sm464w1: L5.u8_at RSEGS M6 (S - 464) fb464) by (clear - AG6 c5_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm464w1]).
  assert (c6_Sm408w1: L5.u8_at RSEGS M6 (S - 408) fb408) by (clear - AG6 c5_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm408w1]).
  assert (c6_Sm280w1: L5.u8_at RSEGS M6 (S - 280) fb280) by (clear - AG6 c5_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm280w1]).
  assert (c6_Sm248w1: L5.u8_at RSEGS M6 (S - 248) fb248) by (clear - AG6 c5_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm248w1]).
  assert (c6_Sm216w1: L5.u8_at RSEGS M6 (S - 216) fb216) by (clear - AG6 c5_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm216w1]).
  assert (c6_Sm192: L5.u64_at RSEGS M6 (S - 192) d3) by (clear - AG6 c5_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm192]).
  assert (c6_Sm200: L5.u64_at RSEGS M6 (S - 200) 8) by (clear - AG6 c5_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm200]).
  assert (c6_Sm184w1: L5.u8_at RSEGS M6 (S - 184) fb184) by (clear - AG6 c5_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm184w1]).
  assert (c6_Sm160: L5.u64_at RSEGS M6 (S - 160) d4) by (clear - AG6 c5_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm160]).
  assert (c6_Sm168: L5.u64_at RSEGS M6 (S - 168) 8) by (clear - AG6 c5_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm168]).
  assert (c6_Sm48w1: L5.u8_at RSEGS M6 (S - 48) fb48) by (clear - AG6 c5_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | exact c5_Sm48w1]).
  assert (c6_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M6 (A + i) 0)) by (clear - AG6 c5_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A; intros i Hi; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | apply c5_Om128z8; exact Hi]).
  assert (c6_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M6 ((A + 48) + i) 0)) by (clear - AG6 c5_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_msg B1_msg B3_msg B4_msg AP_msg_A; intros i Hi; eapply (tr8 M5 M6 _ _ _ (AG6 _ 1)); [lia | apply c5_Om80z12; exact Hi]).
  assert (c6_Sm960: L5.u64_at RSEGS M6 (S - 960) 74669) by (clear - AG6 c5_Sm960 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm960]).
  assert (c6_Sm952: L5.u64_at RSEGS M6 (S - 952) 136012) by (clear - AG6 c5_Sm952 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm952]).
  assert (c6_Sm944: L5.u64_at RSEGS M6 (S - 944) (S - 584)) by (clear - AG6 c5_Sm944 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm944]).
  assert (c6_Sm936: L5.u64_at RSEGS M6 (S - 936) u3_19) by (clear - AG6 c5_Sm936 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm936]).
  assert (c6_Sm928: L5.u64_at RSEGS M6 (S - 928) u3_18) by (clear - AG6 c5_Sm928 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm928]).
  assert (c6_Sm920: L5.u64_at RSEGS M6 (S - 920) u0_9) by (clear - AG6 c5_Sm920 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg; eapply (tr64 M5 M6 _ _ _ (AG6 _ 8)); [lia | exact c5_Sm920]).
  assert (c6_Sm912: L5.u64_at RSEGS M6 (S - 912) (A + 128)) by (cellfix C6_0). clear C6_0.
  assert (c6_Sm904: L5.u64_at RSEGS M6 (S - 904) 136340) by (cellfix C6_1). clear C6_1.
  assert (c6_Gp41w1: L5.u8_at RSEGS M6 (msg + 41) 0) by (cellfix C6_2). clear C6_2.
  assert (c6_Gp0: L5.u64_at RSEGS M6 msg 8028075845441778529) by (cellfix C6_3). clear C6_3.
  assert (c6_Gp8: L5.u64_at RSEGS M6 (msg + 8) 7863351059373564014) by (cellfix C6_4). clear C6_4.
  assert (c6_Gp16: L5.u64_at RSEGS M6 (msg + 16) 2838809733452757089) by (cellfix C6_5). clear C6_5.
  assert (c6_Gp24: L5.u64_at RSEGS M6 (msg + 24) 2334102023183623712) by (cellfix C6_6). clear C6_6.
  assert (c6_Gp32: L5.u64_at RSEGS M6 (msg + 32) 4188416081412519009) by (cellfix C6_7). clear C6_7.
  assert (c6_Gp40w1: L5.u8_at RSEGS M6 (msg + 40) 48) by (cellfix C6_8). clear C6_8.
  assert (c6_Sm880: L5.u64_at RSEGS M6 (S - 880) msg) by (cellfix C6_9). clear C6_9.
  assert (c6_Sm888: L5.u64_at RSEGS M6 (S - 888) 41) by (cellfix C6_10). clear C6_10.
  assert (c6_Sm896: L5.u64_at RSEGS M6 (S - 896) 49) by (cellfix C6_11). clear C6_11.
  assert (STAT6: forall a, stat_rd av a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { clear - FR6 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR6; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (e1_statics_keep M5 M6 gd fl av uid rnd canary hw ES5 STAT6) as ES6.
  assert (DEF6: L5.defined M6 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR6 | exact DEF5]).
  assert (DEFmsg_6: L5.defined M6 msg 48) by (eapply L5.defined_grows; [exact GR6 | exact DEFmsg_5]).
  assert (DEFA_6: L5.defined M6 A 144) by (eapply L5.defined_grows; [exact GR6 | exact DEFA_5]).
  assert (DEFd1_6: L5.defined M6 d1 64) by (eapply L5.defined_grows; [exact GR6 | exact DEFd1_5]).
  assert (DEFd2_6: L5.defined M6 d2 64) by (eapply L5.defined_grows; [exact GR6 | exact DEFd2_5]).
  assert (DEFd3_6: L5.defined M6 d3 64) by (eapply L5.defined_grows; [exact GR6 | exact DEFd3_5]).
  assert (DEFd4_6: L5.defined M6 d4 64) by (eapply L5.defined_grows; [exact GR6 | exact DEFd4_5]).
  assert (HH6: hi_heap HI ((msg, 48) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (cr) 144) 48) M6 (m_vmmaps model5)).
  { clear - HH5 GR6 FR6 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply hi_heap_clientx. exact HH5. lia. 2: exact GR6. intros a Ha.
    destruct (in_dec (S - 1024) (S - 960) a) as [IN0|OUT0]. { right; left; lia. }
    destruct (in_dec (S - 912) (S - 904) a) as [IN1|OUT1]. { right; left; lia. }
    destruct (in_dec (S - 904) (S - 896) a) as [IN2|OUT2]. { right; left; lia. }
    destruct (in_dec (S - 896) (S - 888) a) as [IN3|OUT3]. { right; left; lia. }
    destruct (in_dec (S - 888) (S - 880) a) as [IN4|OUT4]. { right; left; lia. }
    destruct (in_dec (S - 880) (S - 872) a) as [IN5|OUT5]. { right; left; lia. }
    destruct (in_dec msg (msg + 42) a) as [IN6|OUT6]. { right; right; left; exists (msg, 48); split; [left; reflexivity| cbn; lia]. }
    left; apply FR6; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ6: L5C.hpres L LB1 S 10240 XSF M M6).
  { clear - LBWF HQ5 FR6 GR6 IMGHI STOP ERR LY FRSH_msg LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_msg B1_msg B3_msg B4_msg. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M5 M6 [((S - 1024), 64); ((S - 912), 8); ((S - 904), 8); ((S - 896), 8); ((S - 888), 8); ((S - 880), 8); (msg, 42)]). exact LBWF. lia. exact HQ5.
    { intros x Hx. apply FR6; intros Hin.
      - apply (Hx ((S - 1024), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((S - 912), 8)). right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((S - 904), 8)). right; right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((S - 896), 8)). right; right; right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((S - 888), 8)). right; right; right; right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx ((S - 880), 8)). right; right; right; right; right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx (msg, 42)). right; right; right; right; right; right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR6.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. eapply L5PK.wr_fresh. exact FRSH_msg. lia. lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG6 FR6 MS6. try clear STAT6. try clear K5.
  try clear c5_Sm840. try clear c5_Sm848. try clear c5_Sm856. try clear c5_Sm864. try clear c5_Sm872. try clear c5_Sm776. try clear c5_Sm784. try clear c5_Sm792. try clear c5_Sm800. try clear c5_Sm472. try clear c5_Sm480. try clear c5_Sm488. try clear c5_Sm496. try clear c5_Sm504. try clear c5_Sm512. try clear c5_Sm520. try clear c5_Sm528. try clear c5_Sm536. try clear c5_Sm544. try clear c5_Sm552. try clear c5_Sm560. try clear c5_Sm568. try clear c5_Sm424. try clear c5_Sm432. try clear c5_Sm360. try clear c5_Sm368. try clear c5_Sm376. try clear c5_Sm56. try clear c5_Sm64. try clear c5_Sm72. try clear c5_Sm80. try clear c5_Sm88. try clear c5_Sm96. try clear c5_Sm104. try clear c5_Sm112. try clear c5_Sm120. try clear c5_Sm128. try clear c5_Sm136. try clear c5_Sm144. try clear c5_Sm152. try clear c5_Sm8. try clear c5_Sm16. try clear c5_Sm696w1. try clear c5_Sm664w1. try clear c5_Sm640. try clear c5_Sm648. try clear c5_Sm632w1. try clear c5_Sm608. try clear c5_Sm616. try clear c5_Sm600w1. try clear c5_Sm464w1. try clear c5_Sm408w1. try clear c5_Sm280w1. try clear c5_Sm248w1. try clear c5_Sm216w1. try clear c5_Sm192. try clear c5_Sm200. try clear c5_Sm184w1. try clear c5_Sm160. try clear c5_Sm168. try clear c5_Sm48w1. try clear c5_Om128z8. try clear c5_Om80z12. try clear c5_Sm960. try clear c5_Sm952. try clear c5_Sm944. try clear c5_Sm936. try clear c5_Sm928. try clear c5_Sm920. try clear c5_Sm912. try clear c5_Sm904. try clear R5_2. try clear R5_3. try clear R5_4. try clear R5_8. try clear R5_9. try clear R5_18. try clear R5_19. try clear R5_20. try clear R5_10. try clear DEF5. try clear HH5. try clear HQ5. try clear ES5. try clear DEFmsg_5. try clear DEFA_5. try clear DEFd1_5. try clear DEFd2_5. try clear DEFd3_5. try clear DEFd4_5.
  eapply (seg4 fx6 R0 R R6 M M6 model model5 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A msg u0_9 u3_19 u3_18 HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 Wu3_19 Wu3_18 R6_1 R6_2 R6_3 R6_4 R6_8 R6_9 R6_10 R6_11 R6_18 R6_19 R6_20 c6_Sm840 c6_Sm848 c6_Sm856 c6_Sm864 c6_Sm872 c6_Sm776 c6_Sm784 c6_Sm792 c6_Sm800 c6_Sm472 c6_Sm480 c6_Sm488 c6_Sm496 c6_Sm504 c6_Sm512 c6_Sm520 c6_Sm528 c6_Sm536 c6_Sm544 c6_Sm552 c6_Sm560 c6_Sm568 c6_Sm424 c6_Sm432 c6_Sm360 c6_Sm368 c6_Sm376 c6_Sm56 c6_Sm64 c6_Sm72 c6_Sm80 c6_Sm88 c6_Sm96 c6_Sm104 c6_Sm112 c6_Sm120 c6_Sm128 c6_Sm136 c6_Sm144 c6_Sm152 c6_Sm8 c6_Sm16 c6_Sm696w1 c6_Sm664w1 c6_Sm640 c6_Sm648 c6_Sm632w1 c6_Sm608 c6_Sm616 c6_Sm600w1 c6_Sm464w1 c6_Sm408w1 c6_Sm280w1 c6_Sm248w1 c6_Sm216w1 c6_Sm192 c6_Sm200 c6_Sm184w1 c6_Sm160 c6_Sm168 c6_Sm48w1 c6_Om128z8 c6_Om80z12 c6_Sm960 c6_Sm952 c6_Sm944 c6_Sm936 c6_Sm928 c6_Sm920 c6_Sm912 c6_Sm904 c6_Gp41w1 c6_Gp0 c6_Gp8 c6_Gp16 c6_Gp24 c6_Gp32 c6_Gp40w1 c6_Sm880 c6_Sm888 c6_Sm896 ES6 DEF6 DEFmsg_6 DEFA_6 DEFd1_6 DEFd2_6 DEFd3_6 DEFd4_6 BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_msg FRSH_A HH6 MOK5 MBV5 HQ6 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S3.
