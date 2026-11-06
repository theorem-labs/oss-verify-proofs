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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S8.
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
Let seg9 := L5E3S9.seg9 L HI LY LYX HIok.

Lemma seg8 (fx11 : FPState) (R0 R R12 : bvmap 5 word) (M M12 : word -> option byte) (model model12 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref u3_19 u3_18 msg : Z) :
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
  0 <= u3_19 < 2 ^ 64 ->
  0 <= u3_18 < 2 ^ 64 ->
  (* [comment removed for export] *) getr R12 (reg 2) = Z_to_bv 64 (S - 896) ->
  (* [comment removed for export] *) getr R12 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R12 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R12 (reg 8) = Z_to_bv 64 (A + 128) ->
  (* [comment removed for export] *) getr R12 (reg 9) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R12 (reg 18) = Z_to_bv 64 u3_18 ->
  (* [comment removed for export] *) getr R12 (reg 19) = Z_to_bv 64 u3_19 ->
  (* [comment removed for export] *) getr R12 (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M12 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M12 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 880) msg ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 888) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (S - 896) 49 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M12 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M12 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M12 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M12 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M12 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M12 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M12 ref 66 ->
  (* [comment removed for export] *) L5.defined M12 A 144 ->
  (* [comment removed for export] *) L5.defined M12 d1 64 ->
  (* [comment removed for export] *) L5.defined M12 d2 64 ->
  (* [comment removed for export] *) L5.defined M12 d3 64 ->
  (* [comment removed for export] *) L5.defined M12 d4 64 ->
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
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M12 (m_vmmaps model12) ->
  (* [comment removed for export] *) model_ok model12 ->
  (* [comment removed for export] *) model_but_vm model model12 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M12 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx11 R12 136400 M12 model12) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu3_19 Wu3_18 R12_2 R12_3 R12_4 R12_8 R12_9 R12_18 R12_19 R12_20 c12_Sm840 c12_Sm848 c12_Sm856 c12_Sm864 c12_Sm872 c12_Sm776 c12_Sm784 c12_Sm792 c12_Sm800 c12_Sm472 c12_Sm480 c12_Sm488 c12_Sm496 c12_Sm504 c12_Sm512 c12_Sm520 c12_Sm528 c12_Sm536 c12_Sm544 c12_Sm552 c12_Sm560 c12_Sm568 c12_Sm424 c12_Sm432 c12_Sm360 c12_Sm368 c12_Sm376 c12_Sm56 c12_Sm64 c12_Sm72 c12_Sm80 c12_Sm88 c12_Sm96 c12_Sm104 c12_Sm112 c12_Sm120 c12_Sm128 c12_Sm136 c12_Sm144 c12_Sm152 c12_Sm8 c12_Sm16 c12_Sm696w1 c12_Sm664w1 c12_Sm640 c12_Sm648 c12_Sm632w1 c12_Sm608 c12_Sm616 c12_Sm600w1 c12_Sm464w1 c12_Sm408w1 c12_Sm280w1 c12_Sm248w1 c12_Sm216w1 c12_Sm192 c12_Sm200 c12_Sm184w1 c12_Sm160 c12_Sm168 c12_Sm48w1 c12_Om128z8 c12_Om80z12 c12_Sm880 c12_Sm888 c12_Sm896 c12_Op0 c12_Op8 c12_Fp24 c12_Fp32 c12_Fp40 c12_Fp48 c12_Fp56 c12_Fp64w1 c12_Fp65w1 c12_Fp16w4 c12_Fp8 c12_Fp0 c12_Om8 c12_Om40 c12_Om48 c12_Om56 c12_Om64 c12_Om68w4 c12_Om16 c12_Om120 c12_Om24 c12_Om32 c12_Om88 c12_Om104 c12_Om112 c12_Om96 ES12 DEF12 DEFref_12 DEFA_12 DEFd1_12 DEFd2_12 DEFd3_12 DEFd4_12 BR_ref BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH12 MOK12 MBV12 HQ12 KE.
  pose proof MOK12 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  set (u12_10 := U R12 10). assert (Wu12_10: 0 <= u12_10 < 2 ^ 64) by (unfold u12_10, U; apply wrange).
  assert (R12_10: getr R12 (reg 10) = Z_to_bv 64 u12_10) by (unfold u12_10, U; symmetry; apply lit_of_word). clearbody u12_10.
  pose proof ES12 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M12 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p1b_conc fx11 R12 M12 (S - 896) (A + 128) u12_10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx13 & R13 & M13 & MS13 & K13 & R13_2 & R13_9 & R13_10 & R13_11 & FR13 & GR13).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu12_10. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF12); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF12); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_12); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_12); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS13.
  (* [comment removed for export] *)
  assert (AG13: forall a k, ((a + k <= (S - 960) \/ (S - 896) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M12 M13 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR13; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R13_2n: getr R13 (reg 2) = Z_to_bv 64 (S - 896)) by (rewrite R13_2; f_equal; ring). clear R13_2. rename R13_2n into R13_2.
  assert (R13_3: getr R13 (reg 3) = Z_to_bv 64 67584) by (kin K13 3%nat; exact R12_3).
  assert (R13_4: getr R13 (reg 4) = Z_to_bv 64 459832) by (kin K13 4%nat; exact R12_4).
  assert (R13_8: getr R13 (reg 8) = Z_to_bv 64 (A + 128)) by (kin K13 8%nat; exact R12_8).
  assert (R13_9n: getr R13 (reg 9) = Z_to_bv 64 (A + 96)) by (rewrite R13_9; f_equal; ring). clear R13_9. rename R13_9n into R13_9.
  assert (R13_10n: getr R13 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R13_10; f_equal; ring). clear R13_10. rename R13_10n into R13_10.
  assert (R13_18: getr R13 (reg 18) = Z_to_bv 64 u3_18) by (kin K13 18%nat; exact R12_18).
  assert (R13_19: getr R13 (reg 19) = Z_to_bv 64 u3_19) by (kin K13 19%nat; exact R12_19).
  assert (R13_20: getr R13 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K13 20%nat; exact R12_20).
  assert (c13_Sm840: L5.u64_at RSEGS M13 (S - 840) 135392) by (clear - AG13 c12_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm840]).
  assert (c13_Sm848: L5.u64_at RSEGS M13 (S - 848) (S + 64)) by (clear - AG13 c12_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm848]).
  assert (c13_Sm856: L5.u64_at RSEGS M13 (S - 856) w856) by (clear - AG13 c12_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm856]).
  assert (c13_Sm864: L5.u64_at RSEGS M13 (S - 864) w864) by (clear - AG13 c12_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm864]).
  assert (c13_Sm872: L5.u64_at RSEGS M13 (S - 872) w872) by (clear - AG13 c12_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm872]).
  assert (c13_Sm776: L5.u64_at RSEGS M13 (S - 776) 139520) by (clear - AG13 c12_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm776]).
  assert (c13_Sm784: L5.u64_at RSEGS M13 (S - 784) w784) by (clear - AG13 c12_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm784]).
  assert (c13_Sm792: L5.u64_at RSEGS M13 (S - 792) (S + 64)) by (clear - AG13 c12_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm792]).
  assert (c13_Sm800: L5.u64_at RSEGS M13 (S - 800) (S + 64)) by (clear - AG13 c12_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm800]).
  assert (c13_Sm472: L5.u64_at RSEGS M13 (S - 472) 142136) by (clear - AG13 c12_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm472]).
  assert (c13_Sm480: L5.u64_at RSEGS M13 (S - 480) (S + 64)) by (clear - AG13 c12_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm480]).
  assert (c13_Sm488: L5.u64_at RSEGS M13 (S - 488) w488) by (clear - AG13 c12_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm488]).
  assert (c13_Sm496: L5.u64_at RSEGS M13 (S - 496) (S + 64)) by (clear - AG13 c12_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm496]).
  assert (c13_Sm504: L5.u64_at RSEGS M13 (S - 504) w504) by (clear - AG13 c12_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm504]).
  assert (c13_Sm512: L5.u64_at RSEGS M13 (S - 512) w512) by (clear - AG13 c12_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm512]).
  assert (c13_Sm520: L5.u64_at RSEGS M13 (S - 520) w520) by (clear - AG13 c12_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm520]).
  assert (c13_Sm528: L5.u64_at RSEGS M13 (S - 528) w528) by (clear - AG13 c12_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm528]).
  assert (c13_Sm536: L5.u64_at RSEGS M13 (S - 536) w536) by (clear - AG13 c12_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm536]).
  assert (c13_Sm544: L5.u64_at RSEGS M13 (S - 544) w544) by (clear - AG13 c12_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm544]).
  assert (c13_Sm552: L5.u64_at RSEGS M13 (S - 552) w552) by (clear - AG13 c12_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm552]).
  assert (c13_Sm560: L5.u64_at RSEGS M13 (S - 560) w560) by (clear - AG13 c12_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm560]).
  assert (c13_Sm568: L5.u64_at RSEGS M13 (S - 568) w568) by (clear - AG13 c12_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm568]).
  assert (c13_Sm424: L5.u64_at RSEGS M13 (S - 424) 141264) by (clear - AG13 c12_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm424]).
  assert (c13_Sm432: L5.u64_at RSEGS M13 (S - 432) (S + 64)) by (clear - AG13 c12_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm432]).
  assert (c13_Sm360: L5.u64_at RSEGS M13 (S - 360) 139904) by (clear - AG13 c12_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm360]).
  assert (c13_Sm368: L5.u64_at RSEGS M13 (S - 368) (S + 64)) by (clear - AG13 c12_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm368]).
  assert (c13_Sm376: L5.u64_at RSEGS M13 (S - 376) (S - 48)) by (clear - AG13 c12_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm376]).
  assert (c13_Sm56: L5.u64_at RSEGS M13 (S - 56) 138528) by (clear - AG13 c12_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm56]).
  assert (c13_Sm64: L5.u64_at RSEGS M13 (S - 64) (S + 64)) by (clear - AG13 c12_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm64]).
  assert (c13_Sm72: L5.u64_at RSEGS M13 (S - 72) (U R0 9)) by (clear - AG13 c12_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm72]).
  assert (c13_Sm80: L5.u64_at RSEGS M13 (S - 80) (U R0 18)) by (clear - AG13 c12_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm80]).
  assert (c13_Sm88: L5.u64_at RSEGS M13 (S - 88) (U R0 19)) by (clear - AG13 c12_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm88]).
  assert (c13_Sm96: L5.u64_at RSEGS M13 (S - 96) (U R0 20)) by (clear - AG13 c12_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm96]).
  assert (c13_Sm104: L5.u64_at RSEGS M13 (S - 104) (U R0 21)) by (clear - AG13 c12_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm104]).
  assert (c13_Sm112: L5.u64_at RSEGS M13 (S - 112) (U R0 22)) by (clear - AG13 c12_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm112]).
  assert (c13_Sm120: L5.u64_at RSEGS M13 (S - 120) (U R0 23)) by (clear - AG13 c12_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm120]).
  assert (c13_Sm128: L5.u64_at RSEGS M13 (S - 128) (U R0 24)) by (clear - AG13 c12_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm128]).
  assert (c13_Sm136: L5.u64_at RSEGS M13 (S - 136) (U R0 25)) by (clear - AG13 c12_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm136]).
  assert (c13_Sm144: L5.u64_at RSEGS M13 (S - 144) (U R0 26)) by (clear - AG13 c12_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm144]).
  assert (c13_Sm152: L5.u64_at RSEGS M13 (S - 152) (U R0 27)) by (clear - AG13 c12_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm152]).
  assert (c13_Sm8: L5.u64_at RSEGS M13 (S - 8) 132608) by (clear - AG13 c12_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm8]).
  assert (c13_Sm16: L5.u64_at RSEGS M13 (S - 16) (U R0 8)) by (clear - AG13 c12_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm16]).
  assert (c13_Sm696w1: L5.u8_at RSEGS M13 (S - 696) fb696) by (clear - AG13 c12_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm696w1]).
  assert (c13_Sm664w1: L5.u8_at RSEGS M13 (S - 664) fb664) by (clear - AG13 c12_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm664w1]).
  assert (c13_Sm640: L5.u64_at RSEGS M13 (S - 640) d1) by (clear - AG13 c12_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm640]).
  assert (c13_Sm648: L5.u64_at RSEGS M13 (S - 648) 8) by (clear - AG13 c12_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm648]).
  assert (c13_Sm632w1: L5.u8_at RSEGS M13 (S - 632) fb632) by (clear - AG13 c12_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm632w1]).
  assert (c13_Sm608: L5.u64_at RSEGS M13 (S - 608) d2) by (clear - AG13 c12_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm608]).
  assert (c13_Sm616: L5.u64_at RSEGS M13 (S - 616) 8) by (clear - AG13 c12_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm616]).
  assert (c13_Sm600w1: L5.u8_at RSEGS M13 (S - 600) fb600) by (clear - AG13 c12_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm600w1]).
  assert (c13_Sm464w1: L5.u8_at RSEGS M13 (S - 464) fb464) by (clear - AG13 c12_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm464w1]).
  assert (c13_Sm408w1: L5.u8_at RSEGS M13 (S - 408) fb408) by (clear - AG13 c12_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm408w1]).
  assert (c13_Sm280w1: L5.u8_at RSEGS M13 (S - 280) fb280) by (clear - AG13 c12_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm280w1]).
  assert (c13_Sm248w1: L5.u8_at RSEGS M13 (S - 248) fb248) by (clear - AG13 c12_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm248w1]).
  assert (c13_Sm216w1: L5.u8_at RSEGS M13 (S - 216) fb216) by (clear - AG13 c12_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm216w1]).
  assert (c13_Sm192: L5.u64_at RSEGS M13 (S - 192) d3) by (clear - AG13 c12_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm192]).
  assert (c13_Sm200: L5.u64_at RSEGS M13 (S - 200) 8) by (clear - AG13 c12_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm200]).
  assert (c13_Sm184w1: L5.u8_at RSEGS M13 (S - 184) fb184) by (clear - AG13 c12_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm184w1]).
  assert (c13_Sm160: L5.u64_at RSEGS M13 (S - 160) d4) by (clear - AG13 c12_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm160]).
  assert (c13_Sm168: L5.u64_at RSEGS M13 (S - 168) 8) by (clear - AG13 c12_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm168]).
  assert (c13_Sm48w1: L5.u8_at RSEGS M13 (S - 48) fb48) by (clear - AG13 c12_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Sm48w1]).
  assert (c13_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M13 (A + i) 0)) by (clear - AG13 c12_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | apply c12_Om128z8; exact Hi]).
  assert (c13_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M13 ((A + 48) + i) 0)) by (clear - AG13 c12_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | apply c12_Om80z12; exact Hi]).
  assert (c13_Sm880: L5.u64_at RSEGS M13 (S - 880) msg) by (clear - AG13 c12_Sm880 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm880]).
  assert (c13_Sm888: L5.u64_at RSEGS M13 (S - 888) 41) by (clear - AG13 c12_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm888]).
  assert (c13_Sm896: L5.u64_at RSEGS M13 (S - 896) 49) by (clear - AG13 c12_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Sm896]).
  assert (c13_Op0: L5.u64_at RSEGS M13 (A + 128) 373272) by (clear - AG13 c12_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Op0]).
  assert (c13_Op8: L5.u64_at RSEGS M13 (A + 136) (ref + 24)) by (clear - AG13 c12_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Op8]).
  assert (c13_Fp24: L5.u64_at RSEGS M13 (ref + 24) 8028075845441778529) by (clear - AG13 c12_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp24]).
  assert (c13_Fp32: L5.u64_at RSEGS M13 (ref + 32) 7863351059373564014) by (clear - AG13 c12_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp32]).
  assert (c13_Fp40: L5.u64_at RSEGS M13 (ref + 40) 2838809733452757089) by (clear - AG13 c12_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp40]).
  assert (c13_Fp48: L5.u64_at RSEGS M13 (ref + 48) 2334102023183623712) by (clear - AG13 c12_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp48]).
  assert (c13_Fp56: L5.u64_at RSEGS M13 (ref + 56) 4188416081412519009) by (clear - AG13 c12_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp56]).
  assert (c13_Fp64w1: L5.u8_at RSEGS M13 (ref + 64) 48) by (clear - AG13 c12_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Fp64w1]).
  assert (c13_Fp65w1: L5.u8_at RSEGS M13 (ref + 65) 0) by (clear - AG13 c12_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M12 M13 _ _ _ (AG13 _ 1)); [lia | exact c12_Fp65w1]).
  assert (c13_Fp16w4: L5.u32_at RSEGS M13 (ref + 16) 0) by (clear - AG13 c12_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M12 M13 _ _ _ (AG13 _ 4)); [lia | exact c12_Fp16w4]).
  assert (c13_Fp8: L5.u64_at RSEGS M13 (ref + 8) 41) by (clear - AG13 c12_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp8]).
  assert (c13_Fp0: L5.u64_at RSEGS M13 ref 41) by (clear - AG13 c12_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Fp0]).
  assert (c13_Om8: L5.u64_at RSEGS M13 (A + 120) S) by (clear - AG13 c12_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om8]).
  assert (c13_Om40: L5.u64_at RSEGS M13 (A + 88) (A + 128)) by (clear - AG13 c12_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om40]).
  assert (c13_Om48: L5.u64_at RSEGS M13 (A + 80) 133016) by (clear - AG13 c12_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om48]).
  assert (c13_Om56: L5.u64_at RSEGS M13 (A + 72) 91560) by (clear - AG13 c12_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om56]).
  assert (c13_Om64: L5.u64_at RSEGS M13 (A + 64) 91699) by (clear - AG13 c12_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om64]).
  assert (c13_Om68w4: L5.u32_at RSEGS M13 (A + 60) 1) by (clear - AG13 c12_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M12 M13 _ _ _ (AG13 _ 4)); [lia | exact c12_Om68w4]).
  assert (c13_Om16: L5.u64_at RSEGS M13 (A + 112) 0) by (clear - AG13 c12_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om16]).
  assert (c13_Om120: L5.u64_at RSEGS M13 (A + 8) 1) by (clear - AG13 c12_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om120]).
  assert (c13_Om24: L5.u64_at RSEGS M13 (A + 104) 257624) by (clear - AG13 c12_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om24]).
  assert (c13_Om32: L5.u64_at RSEGS M13 (A + 96) 4849336966747728640) by (clear - AG13 c12_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om32]).
  assert (c13_Om88: L5.u64_at RSEGS M13 (A + 40) 142700) by (clear - AG13 c12_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om88]).
  assert (c13_Om104: L5.u64_at RSEGS M13 (A + 24) 253816) by (clear - AG13 c12_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om104]).
  assert (c13_Om112: L5.u64_at RSEGS M13 (A + 16) 373232) by (clear - AG13 c12_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om112]).
  assert (c13_Om96: L5.u64_at RSEGS M13 (A + 32) 142968) by (clear - AG13 c12_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M12 M13 _ _ _ (AG13 _ 8)); [lia | exact c12_Om96]).
  assert (STAT13: forall a, stat_rd av a -> M13 (Z_to_bv 64 a) = M12 (Z_to_bv 64 a)).
  { clear - FR13 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR13; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M12 M13 gd av uid rnd canary hw ES12 STAT13) as ES13.
  assert (DEF13: L5.defined M13 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR13 | exact DEF12]).
  assert (DEFref_13: L5.defined M13 ref 66) by (eapply L5.defined_grows; [exact GR13 | exact DEFref_12]).
  assert (DEFA_13: L5.defined M13 A 144) by (eapply L5.defined_grows; [exact GR13 | exact DEFA_12]).
  assert (DEFd1_13: L5.defined M13 d1 64) by (eapply L5.defined_grows; [exact GR13 | exact DEFd1_12]).
  assert (DEFd2_13: L5.defined M13 d2 64) by (eapply L5.defined_grows; [exact GR13 | exact DEFd2_12]).
  assert (DEFd3_13: L5.defined M13 d3 64) by (eapply L5.defined_grows; [exact GR13 | exact DEFd3_12]).
  assert (DEFd4_13: L5.defined M13 d4 64) by (eapply L5.defined_grows; [exact GR13 | exact DEFd4_12]).
  assert (HH13: hi_heap HI ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M13 (m_vmmaps model12)).
  { clear - HH12 GR13 FR13 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH12. lia. 2: exact GR13. intros a Ha.
    destruct (in_dec (S - 960) (S - 896) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR13; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ13: L5C.hpres L LB1 S 10240 XSF M M13).
  { clear - LBWF HQ12 FR13 GR13 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M12 M13 [((S - 960), 64)]). exact LBWF. lia. exact HQ12.
    { intros x Hx. apply FR13; intros Hin.
        apply (Hx ((S - 960), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR13.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG13 FR13 MS13. try clear STAT13. try clear K12.
  try clear c12_Sm840. try clear c12_Sm848. try clear c12_Sm856. try clear c12_Sm864. try clear c12_Sm872. try clear c12_Sm776. try clear c12_Sm784. try clear c12_Sm792. try clear c12_Sm800. try clear c12_Sm472. try clear c12_Sm480. try clear c12_Sm488. try clear c12_Sm496. try clear c12_Sm504. try clear c12_Sm512. try clear c12_Sm520. try clear c12_Sm528. try clear c12_Sm536. try clear c12_Sm544. try clear c12_Sm552. try clear c12_Sm560. try clear c12_Sm568. try clear c12_Sm424. try clear c12_Sm432. try clear c12_Sm360. try clear c12_Sm368. try clear c12_Sm376. try clear c12_Sm56. try clear c12_Sm64. try clear c12_Sm72. try clear c12_Sm80. try clear c12_Sm88. try clear c12_Sm96. try clear c12_Sm104. try clear c12_Sm112. try clear c12_Sm120. try clear c12_Sm128. try clear c12_Sm136. try clear c12_Sm144. try clear c12_Sm152. try clear c12_Sm8. try clear c12_Sm16. try clear c12_Sm696w1. try clear c12_Sm664w1. try clear c12_Sm640. try clear c12_Sm648. try clear c12_Sm632w1. try clear c12_Sm608. try clear c12_Sm616. try clear c12_Sm600w1. try clear c12_Sm464w1. try clear c12_Sm408w1. try clear c12_Sm280w1. try clear c12_Sm248w1. try clear c12_Sm216w1. try clear c12_Sm192. try clear c12_Sm200. try clear c12_Sm184w1. try clear c12_Sm160. try clear c12_Sm168. try clear c12_Sm48w1. try clear c12_Om128z8. try clear c12_Om80z12. try clear c12_Sm880. try clear c12_Sm888. try clear c12_Sm896. try clear c12_Op0. try clear c12_Op8. try clear c12_Fp24. try clear c12_Fp32. try clear c12_Fp40. try clear c12_Fp48. try clear c12_Fp56. try clear c12_Fp64w1. try clear c12_Fp65w1. try clear c12_Fp16w4. try clear c12_Fp8. try clear c12_Fp0. try clear c12_Om8. try clear c12_Om40. try clear c12_Om48. try clear c12_Om56. try clear c12_Om64. try clear c12_Om68w4. try clear c12_Om16. try clear c12_Om120. try clear c12_Om24. try clear c12_Om32. try clear c12_Om88. try clear c12_Om104. try clear c12_Om112. try clear c12_Om96. try clear R12_2. try clear R12_3. try clear R12_4. try clear R12_8. try clear R12_9. try clear R12_18. try clear R12_19. try clear R12_20. try clear R12_10. try clear DEF12. try clear HH12. try clear HQ12. try clear ES12. try clear DEFref_12. try clear DEFA_12. try clear DEFd1_12. try clear DEFd2_12. try clear DEFd3_12. try clear DEFd4_12.
  (* [comment removed for export] *)
  pose proof ES13 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M13 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r1_conc fx13 R13 M13 (S - 896) (A + 128) av canary uid rnd hw w856 w864 w872 w784 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx14 & R14 & M14 & MS14 & K14 & R14_1 & R14_2 & R14_8 & R14_9 & R14_10 & R14_11 & R14_18 & R14_19 & FR14 & GR14).
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
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww856. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww864. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww872. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Ww784. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF13 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF13); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF13 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF13); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_13 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_13); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_13 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_13); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c13_Om16 | cellfix c13_Om16]. }
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
  { (* [comment removed for export] *) first [exact c13_Om8 | cellfix c13_Om8]. }
  { (* [comment removed for export] *) first [exact c13_Om32 | cellfix c13_Om32]. }
  { (* [comment removed for export] *) first [exact c13_Sm840 | cellfix c13_Sm840]. }
  { (* [comment removed for export] *) first [exact c13_Sm848 | cellfix c13_Sm848]. }
  { (* [comment removed for export] *) first [exact c13_Sm856 | cellfix c13_Sm856]. }
  { (* [comment removed for export] *) first [exact c13_Sm864 | cellfix c13_Sm864]. }
  { (* [comment removed for export] *) first [exact c13_Sm872 | cellfix c13_Sm872]. }
  { (* [comment removed for export] *) first [exact c13_Sm776 | cellfix c13_Sm776]. }
  { (* [comment removed for export] *) first [exact c13_Sm784 | cellfix c13_Sm784]. }
  { (* [comment removed for export] *) first [exact c13_Sm792 | cellfix c13_Sm792]. }
  { (* [comment removed for export] *) first [exact c13_Sm800 | cellfix c13_Sm800]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS14.
  (* [comment removed for export] *)
  assert (AG14: forall a k, ((a + k <= (S - 8832) \/ (S - 896) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M13 M14 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR14; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R14_1n: getr R14 (reg 1) = Z_to_bv 64 140248) by (rewrite R14_1; f_equal; ring). clear R14_1. rename R14_1n into R14_1.
  assert (R14_2n: getr R14 (reg 2) = Z_to_bv 64 (S - 768)) by (rewrite R14_2; f_equal; ring). clear R14_2. rename R14_2n into R14_2.
  assert (R14_3: getr R14 (reg 3) = Z_to_bv 64 67584) by (kin K14 3%nat; exact R13_3).
  assert (R14_4: getr R14 (reg 4) = Z_to_bv 64 459832) by (kin K14 4%nat; exact R13_4).
  assert (R14_8n: getr R14 (reg 8) = Z_to_bv 64 w784) by (rewrite R14_8; f_equal; ring). clear R14_8. rename R14_8n into R14_8.
  assert (R14_9n: getr R14 (reg 9) = Z_to_bv 64 (S + 64)) by (rewrite R14_9; f_equal; ring). clear R14_9. rename R14_9n into R14_9.
  assert (R14_10n: getr R14 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R14_10; f_equal; ring). clear R14_10. rename R14_10n into R14_10.
  assert (R14_11n: getr R14 (reg 11) = Z_to_bv 64 0) by (rewrite R14_11; f_equal; ring). clear R14_11. rename R14_11n into R14_11.
  assert (R14_18n: getr R14 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite R14_18; f_equal; ring). clear R14_18. rename R14_18n into R14_18.
  assert (R14_19n: getr R14 (reg 19) = Z_to_bv 64 w872) by (rewrite R14_19; f_equal; ring). clear R14_19. rename R14_19n into R14_19.
  assert (R14_20: getr R14 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K14 20%nat; exact R13_20).
  assert (c14_Sm840: L5.u64_at RSEGS M14 (S - 840) 135392) by (clear - AG14 c13_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm840]).
  assert (c14_Sm848: L5.u64_at RSEGS M14 (S - 848) (S + 64)) by (clear - AG14 c13_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm848]).
  assert (c14_Sm856: L5.u64_at RSEGS M14 (S - 856) w856) by (clear - AG14 c13_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm856]).
  assert (c14_Sm864: L5.u64_at RSEGS M14 (S - 864) w864) by (clear - AG14 c13_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm864]).
  assert (c14_Sm872: L5.u64_at RSEGS M14 (S - 872) w872) by (clear - AG14 c13_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm872]).
  assert (c14_Sm776: L5.u64_at RSEGS M14 (S - 776) 139520) by (clear - AG14 c13_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm776]).
  assert (c14_Sm784: L5.u64_at RSEGS M14 (S - 784) w784) by (clear - AG14 c13_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm784]).
  assert (c14_Sm792: L5.u64_at RSEGS M14 (S - 792) (S + 64)) by (clear - AG14 c13_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm792]).
  assert (c14_Sm800: L5.u64_at RSEGS M14 (S - 800) (S + 64)) by (clear - AG14 c13_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm800]).
  assert (c14_Sm472: L5.u64_at RSEGS M14 (S - 472) 142136) by (clear - AG14 c13_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm472]).
  assert (c14_Sm480: L5.u64_at RSEGS M14 (S - 480) (S + 64)) by (clear - AG14 c13_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm480]).
  assert (c14_Sm488: L5.u64_at RSEGS M14 (S - 488) w488) by (clear - AG14 c13_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm488]).
  assert (c14_Sm496: L5.u64_at RSEGS M14 (S - 496) (S + 64)) by (clear - AG14 c13_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm496]).
  assert (c14_Sm504: L5.u64_at RSEGS M14 (S - 504) w504) by (clear - AG14 c13_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm504]).
  assert (c14_Sm512: L5.u64_at RSEGS M14 (S - 512) w512) by (clear - AG14 c13_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm512]).
  assert (c14_Sm520: L5.u64_at RSEGS M14 (S - 520) w520) by (clear - AG14 c13_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm520]).
  assert (c14_Sm528: L5.u64_at RSEGS M14 (S - 528) w528) by (clear - AG14 c13_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm528]).
  assert (c14_Sm536: L5.u64_at RSEGS M14 (S - 536) w536) by (clear - AG14 c13_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm536]).
  assert (c14_Sm544: L5.u64_at RSEGS M14 (S - 544) w544) by (clear - AG14 c13_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm544]).
  assert (c14_Sm552: L5.u64_at RSEGS M14 (S - 552) w552) by (clear - AG14 c13_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm552]).
  assert (c14_Sm560: L5.u64_at RSEGS M14 (S - 560) w560) by (clear - AG14 c13_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm560]).
  assert (c14_Sm568: L5.u64_at RSEGS M14 (S - 568) w568) by (clear - AG14 c13_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm568]).
  assert (c14_Sm424: L5.u64_at RSEGS M14 (S - 424) 141264) by (clear - AG14 c13_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm424]).
  assert (c14_Sm432: L5.u64_at RSEGS M14 (S - 432) (S + 64)) by (clear - AG14 c13_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm432]).
  assert (c14_Sm360: L5.u64_at RSEGS M14 (S - 360) 139904) by (clear - AG14 c13_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm360]).
  assert (c14_Sm368: L5.u64_at RSEGS M14 (S - 368) (S + 64)) by (clear - AG14 c13_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm368]).
  assert (c14_Sm376: L5.u64_at RSEGS M14 (S - 376) (S - 48)) by (clear - AG14 c13_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm376]).
  assert (c14_Sm56: L5.u64_at RSEGS M14 (S - 56) 138528) by (clear - AG14 c13_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm56]).
  assert (c14_Sm64: L5.u64_at RSEGS M14 (S - 64) (S + 64)) by (clear - AG14 c13_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm64]).
  assert (c14_Sm72: L5.u64_at RSEGS M14 (S - 72) (U R0 9)) by (clear - AG14 c13_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm72]).
  assert (c14_Sm80: L5.u64_at RSEGS M14 (S - 80) (U R0 18)) by (clear - AG14 c13_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm80]).
  assert (c14_Sm88: L5.u64_at RSEGS M14 (S - 88) (U R0 19)) by (clear - AG14 c13_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm88]).
  assert (c14_Sm96: L5.u64_at RSEGS M14 (S - 96) (U R0 20)) by (clear - AG14 c13_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm96]).
  assert (c14_Sm104: L5.u64_at RSEGS M14 (S - 104) (U R0 21)) by (clear - AG14 c13_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm104]).
  assert (c14_Sm112: L5.u64_at RSEGS M14 (S - 112) (U R0 22)) by (clear - AG14 c13_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm112]).
  assert (c14_Sm120: L5.u64_at RSEGS M14 (S - 120) (U R0 23)) by (clear - AG14 c13_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm120]).
  assert (c14_Sm128: L5.u64_at RSEGS M14 (S - 128) (U R0 24)) by (clear - AG14 c13_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm128]).
  assert (c14_Sm136: L5.u64_at RSEGS M14 (S - 136) (U R0 25)) by (clear - AG14 c13_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm136]).
  assert (c14_Sm144: L5.u64_at RSEGS M14 (S - 144) (U R0 26)) by (clear - AG14 c13_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm144]).
  assert (c14_Sm152: L5.u64_at RSEGS M14 (S - 152) (U R0 27)) by (clear - AG14 c13_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm152]).
  assert (c14_Sm8: L5.u64_at RSEGS M14 (S - 8) 132608) by (clear - AG14 c13_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm8]).
  assert (c14_Sm16: L5.u64_at RSEGS M14 (S - 16) (U R0 8)) by (clear - AG14 c13_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm16]).
  assert (c14_Sm696w1: L5.u8_at RSEGS M14 (S - 696) fb696) by (clear - AG14 c13_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm696w1]).
  assert (c14_Sm664w1: L5.u8_at RSEGS M14 (S - 664) fb664) by (clear - AG14 c13_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm664w1]).
  assert (c14_Sm640: L5.u64_at RSEGS M14 (S - 640) d1) by (clear - AG14 c13_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm640]).
  assert (c14_Sm648: L5.u64_at RSEGS M14 (S - 648) 8) by (clear - AG14 c13_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm648]).
  assert (c14_Sm632w1: L5.u8_at RSEGS M14 (S - 632) fb632) by (clear - AG14 c13_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm632w1]).
  assert (c14_Sm608: L5.u64_at RSEGS M14 (S - 608) d2) by (clear - AG14 c13_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm608]).
  assert (c14_Sm616: L5.u64_at RSEGS M14 (S - 616) 8) by (clear - AG14 c13_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm616]).
  assert (c14_Sm600w1: L5.u8_at RSEGS M14 (S - 600) fb600) by (clear - AG14 c13_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm600w1]).
  assert (c14_Sm464w1: L5.u8_at RSEGS M14 (S - 464) fb464) by (clear - AG14 c13_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm464w1]).
  assert (c14_Sm408w1: L5.u8_at RSEGS M14 (S - 408) fb408) by (clear - AG14 c13_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm408w1]).
  assert (c14_Sm280w1: L5.u8_at RSEGS M14 (S - 280) fb280) by (clear - AG14 c13_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm280w1]).
  assert (c14_Sm248w1: L5.u8_at RSEGS M14 (S - 248) fb248) by (clear - AG14 c13_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm248w1]).
  assert (c14_Sm216w1: L5.u8_at RSEGS M14 (S - 216) fb216) by (clear - AG14 c13_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm216w1]).
  assert (c14_Sm192: L5.u64_at RSEGS M14 (S - 192) d3) by (clear - AG14 c13_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm192]).
  assert (c14_Sm200: L5.u64_at RSEGS M14 (S - 200) 8) by (clear - AG14 c13_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm200]).
  assert (c14_Sm184w1: L5.u8_at RSEGS M14 (S - 184) fb184) by (clear - AG14 c13_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm184w1]).
  assert (c14_Sm160: L5.u64_at RSEGS M14 (S - 160) d4) by (clear - AG14 c13_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm160]).
  assert (c14_Sm168: L5.u64_at RSEGS M14 (S - 168) 8) by (clear - AG14 c13_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm168]).
  assert (c14_Sm48w1: L5.u8_at RSEGS M14 (S - 48) fb48) by (clear - AG14 c13_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Sm48w1]).
  assert (c14_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M14 (A + i) 0)) by (clear - AG14 c13_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | apply c13_Om128z8; exact Hi]).
  assert (c14_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M14 ((A + 48) + i) 0)) by (clear - AG14 c13_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | apply c13_Om80z12; exact Hi]).
  assert (c14_Sm880: L5.u64_at RSEGS M14 (S - 880) msg) by (clear - AG14 c13_Sm880 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm880]).
  assert (c14_Sm888: L5.u64_at RSEGS M14 (S - 888) 41) by (clear - AG14 c13_Sm888 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm888]).
  assert (c14_Sm896: L5.u64_at RSEGS M14 (S - 896) 49) by (clear - AG14 c13_Sm896 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Sm896]).
  assert (c14_Op0: L5.u64_at RSEGS M14 (A + 128) 373272) by (clear - AG14 c13_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Op0]).
  assert (c14_Op8: L5.u64_at RSEGS M14 (A + 136) (ref + 24)) by (clear - AG14 c13_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Op8]).
  assert (c14_Fp24: L5.u64_at RSEGS M14 (ref + 24) 8028075845441778529) by (clear - AG14 c13_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp24]).
  assert (c14_Fp32: L5.u64_at RSEGS M14 (ref + 32) 7863351059373564014) by (clear - AG14 c13_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp32]).
  assert (c14_Fp40: L5.u64_at RSEGS M14 (ref + 40) 2838809733452757089) by (clear - AG14 c13_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp40]).
  assert (c14_Fp48: L5.u64_at RSEGS M14 (ref + 48) 2334102023183623712) by (clear - AG14 c13_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp48]).
  assert (c14_Fp56: L5.u64_at RSEGS M14 (ref + 56) 4188416081412519009) by (clear - AG14 c13_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp56]).
  assert (c14_Fp64w1: L5.u8_at RSEGS M14 (ref + 64) 48) by (clear - AG14 c13_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Fp64w1]).
  assert (c14_Fp65w1: L5.u8_at RSEGS M14 (ref + 65) 0) by (clear - AG14 c13_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M13 M14 _ _ _ (AG14 _ 1)); [lia | exact c13_Fp65w1]).
  assert (c14_Fp16w4: L5.u32_at RSEGS M14 (ref + 16) 0) by (clear - AG14 c13_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M13 M14 _ _ _ (AG14 _ 4)); [lia | exact c13_Fp16w4]).
  assert (c14_Fp8: L5.u64_at RSEGS M14 (ref + 8) 41) by (clear - AG14 c13_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp8]).
  assert (c14_Fp0: L5.u64_at RSEGS M14 ref 41) by (clear - AG14 c13_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Fp0]).
  assert (c14_Om8: L5.u64_at RSEGS M14 (A + 120) S) by (clear - AG14 c13_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om8]).
  assert (c14_Om40: L5.u64_at RSEGS M14 (A + 88) (A + 128)) by (clear - AG14 c13_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om40]).
  assert (c14_Om48: L5.u64_at RSEGS M14 (A + 80) 133016) by (clear - AG14 c13_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om48]).
  assert (c14_Om56: L5.u64_at RSEGS M14 (A + 72) 91560) by (clear - AG14 c13_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om56]).
  assert (c14_Om64: L5.u64_at RSEGS M14 (A + 64) 91699) by (clear - AG14 c13_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om64]).
  assert (c14_Om68w4: L5.u32_at RSEGS M14 (A + 60) 1) by (clear - AG14 c13_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M13 M14 _ _ _ (AG14 _ 4)); [lia | exact c13_Om68w4]).
  assert (c14_Om16: L5.u64_at RSEGS M14 (A + 112) 0) by (clear - AG14 c13_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om16]).
  assert (c14_Om120: L5.u64_at RSEGS M14 (A + 8) 1) by (clear - AG14 c13_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om120]).
  assert (c14_Om24: L5.u64_at RSEGS M14 (A + 104) 257624) by (clear - AG14 c13_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om24]).
  assert (c14_Om32: L5.u64_at RSEGS M14 (A + 96) 4849336966747728640) by (clear - AG14 c13_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om32]).
  assert (c14_Om88: L5.u64_at RSEGS M14 (A + 40) 142700) by (clear - AG14 c13_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om88]).
  assert (c14_Om104: L5.u64_at RSEGS M14 (A + 24) 253816) by (clear - AG14 c13_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om104]).
  assert (c14_Om112: L5.u64_at RSEGS M14 (A + 16) 373232) by (clear - AG14 c13_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om112]).
  assert (c14_Om96: L5.u64_at RSEGS M14 (A + 32) 142968) by (clear - AG14 c13_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M13 M14 _ _ _ (AG14 _ 8)); [lia | exact c13_Om96]).
  assert (STAT14: forall a, stat_rd av a -> M14 (Z_to_bv 64 a) = M13 (Z_to_bv 64 a)).
  { clear - FR14 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR14; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M13 M14 gd av uid rnd canary hw ES13 STAT14) as ES14.
  assert (DEF14: L5.defined M14 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR14 | exact DEF13]).
  assert (DEFref_14: L5.defined M14 ref 66) by (eapply L5.defined_grows; [exact GR14 | exact DEFref_13]).
  assert (DEFA_14: L5.defined M14 A 144) by (eapply L5.defined_grows; [exact GR14 | exact DEFA_13]).
  assert (DEFd1_14: L5.defined M14 d1 64) by (eapply L5.defined_grows; [exact GR14 | exact DEFd1_13]).
  assert (DEFd2_14: L5.defined M14 d2 64) by (eapply L5.defined_grows; [exact GR14 | exact DEFd2_13]).
  assert (DEFd3_14: L5.defined M14 d3 64) by (eapply L5.defined_grows; [exact GR14 | exact DEFd3_13]).
  assert (DEFd4_14: L5.defined M14 d4 64) by (eapply L5.defined_grows; [exact GR14 | exact DEFd4_13]).
  assert (HH14: hi_heap HI ((ref, 66) :: (A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M14 (m_vmmaps model12)).
  { clear - HH13 GR14 FR14 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH13. lia. 2: exact GR14. intros a Ha.
    destruct (in_dec (S - 8832) (S - 896) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR14; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ14: L5C.hpres L LB1 S 10240 XSF M M14).
  { clear - LBWF HQ13 FR14 GR14 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M13 M14 [((S - 8832), 7936)]). exact LBWF. lia. exact HQ13.
    { intros x Hx. apply FR14; intros Hin.
        apply (Hx ((S - 8832), 7936)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR14.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG14 FR14 MS14. try clear STAT14. try clear K13.
  try clear c13_Sm840. try clear c13_Sm848. try clear c13_Sm856. try clear c13_Sm864. try clear c13_Sm872. try clear c13_Sm776. try clear c13_Sm784. try clear c13_Sm792. try clear c13_Sm800. try clear c13_Sm472. try clear c13_Sm480. try clear c13_Sm488. try clear c13_Sm496. try clear c13_Sm504. try clear c13_Sm512. try clear c13_Sm520. try clear c13_Sm528. try clear c13_Sm536. try clear c13_Sm544. try clear c13_Sm552. try clear c13_Sm560. try clear c13_Sm568. try clear c13_Sm424. try clear c13_Sm432. try clear c13_Sm360. try clear c13_Sm368. try clear c13_Sm376. try clear c13_Sm56. try clear c13_Sm64. try clear c13_Sm72. try clear c13_Sm80. try clear c13_Sm88. try clear c13_Sm96. try clear c13_Sm104. try clear c13_Sm112. try clear c13_Sm120. try clear c13_Sm128. try clear c13_Sm136. try clear c13_Sm144. try clear c13_Sm152. try clear c13_Sm8. try clear c13_Sm16. try clear c13_Sm696w1. try clear c13_Sm664w1. try clear c13_Sm640. try clear c13_Sm648. try clear c13_Sm632w1. try clear c13_Sm608. try clear c13_Sm616. try clear c13_Sm600w1. try clear c13_Sm464w1. try clear c13_Sm408w1. try clear c13_Sm280w1. try clear c13_Sm248w1. try clear c13_Sm216w1. try clear c13_Sm192. try clear c13_Sm200. try clear c13_Sm184w1. try clear c13_Sm160. try clear c13_Sm168. try clear c13_Sm48w1. try clear c13_Om128z8. try clear c13_Om80z12. try clear c13_Sm880. try clear c13_Sm888. try clear c13_Sm896. try clear c13_Op0. try clear c13_Op8. try clear c13_Fp24. try clear c13_Fp32. try clear c13_Fp40. try clear c13_Fp48. try clear c13_Fp56. try clear c13_Fp64w1. try clear c13_Fp65w1. try clear c13_Fp16w4. try clear c13_Fp8. try clear c13_Fp0. try clear c13_Om8. try clear c13_Om40. try clear c13_Om48. try clear c13_Om56. try clear c13_Om64. try clear c13_Om68w4. try clear c13_Om16. try clear c13_Om120. try clear c13_Om24. try clear c13_Om32. try clear c13_Om88. try clear c13_Om104. try clear c13_Om112. try clear c13_Om96. try clear R13_2. try clear R13_3. try clear R13_4. try clear R13_8. try clear R13_9. try clear R13_10. try clear R13_18. try clear R13_19. try clear R13_20. try clear DEF13. try clear HH13. try clear HQ13. try clear ES13. try clear DEFref_13. try clear DEFA_13. try clear DEFd1_13. try clear DEFd2_13. try clear DEFd3_13. try clear DEFd4_13.
  eapply (seg9 fx14 R0 R R14 M M14 model model12 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref msg HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R14_1 R14_2 R14_3 R14_4 R14_8 R14_9 R14_10 R14_11 R14_18 R14_19 R14_20 c14_Sm840 c14_Sm848 c14_Sm856 c14_Sm864 c14_Sm872 c14_Sm776 c14_Sm784 c14_Sm792 c14_Sm800 c14_Sm472 c14_Sm480 c14_Sm488 c14_Sm496 c14_Sm504 c14_Sm512 c14_Sm520 c14_Sm528 c14_Sm536 c14_Sm544 c14_Sm552 c14_Sm560 c14_Sm568 c14_Sm424 c14_Sm432 c14_Sm360 c14_Sm368 c14_Sm376 c14_Sm56 c14_Sm64 c14_Sm72 c14_Sm80 c14_Sm88 c14_Sm96 c14_Sm104 c14_Sm112 c14_Sm120 c14_Sm128 c14_Sm136 c14_Sm144 c14_Sm152 c14_Sm8 c14_Sm16 c14_Sm696w1 c14_Sm664w1 c14_Sm640 c14_Sm648 c14_Sm632w1 c14_Sm608 c14_Sm616 c14_Sm600w1 c14_Sm464w1 c14_Sm408w1 c14_Sm280w1 c14_Sm248w1 c14_Sm216w1 c14_Sm192 c14_Sm200 c14_Sm184w1 c14_Sm160 c14_Sm168 c14_Sm48w1 c14_Om128z8 c14_Om80z12 c14_Sm880 c14_Sm888 c14_Sm896 c14_Op0 c14_Op8 c14_Fp24 c14_Fp32 c14_Fp40 c14_Fp48 c14_Fp56 c14_Fp64w1 c14_Fp65w1 c14_Fp16w4 c14_Fp8 c14_Fp0 c14_Om8 c14_Om40 c14_Om48 c14_Om56 c14_Om64 c14_Om68w4 c14_Om16 c14_Om120 c14_Om24 c14_Om32 c14_Om88 c14_Om104 c14_Om112 c14_Om96 ES14 DEF14 DEFref_14 DEFA_14 DEFd1_14 DEFd2_14 DEFd3_14 DEFd4_14 BR_ref BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_ref_A AP_ref_d1 AP_ref_d2 AP_ref_d3 AP_ref_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_ref FRSH_A HH14 MOK12 MBV12 HQ14 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S8.
