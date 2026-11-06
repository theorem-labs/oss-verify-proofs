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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S16.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S15.
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
Let seg16 := L5E3S16.seg16 L HI LY LYX HIok.

Lemma seg15 (fx25 : FPState) (R0 R R26 : bvmap 5 word) (M M26 : word -> option byte) (model model26 : Model) (K : TSet)
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
  (* [comment removed for export] *) getr R26 (reg 2) = Z_to_bv 64 (S - 352) ->
  (* [comment removed for export] *) getr R26 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R26 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R26 (reg 8) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R26 (reg 9) = Z_to_bv 64 (S - 48) ->
  (* [comment removed for export] *) getr R26 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R26 (reg 19) = Z_to_bv 64 w504 ->
  (* [comment removed for export] *) getr R26 (reg 20) = Z_to_bv 64 w512 ->
  (* [comment removed for export] *) getr R26 (reg 21) = Z_to_bv 64 w520 ->
  (* [comment removed for export] *) getr R26 (reg 22) = Z_to_bv 64 w528 ->
  (* [comment removed for export] *) getr R26 (reg 23) = Z_to_bv 64 w536 ->
  (* [comment removed for export] *) getr R26 (reg 24) = Z_to_bv 64 w544 ->
  (* [comment removed for export] *) getr R26 (reg 25) = Z_to_bv 64 w552 ->
  (* [comment removed for export] *) getr R26 (reg 26) = Z_to_bv 64 w560 ->
  (* [comment removed for export] *) getr R26 (reg 27) = Z_to_bv 64 w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M26 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M26 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M26 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M26 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M26 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M26 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M26 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M26 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M26 ref 66 ->
  (* [comment removed for export] *) L5.defined M26 A 144 ->
  (* [comment removed for export] *) L5.defined M26 d4 64 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) (ref + 66 <= d4 \/ d4 + 64 <= ref) ->
  (* [comment removed for export] *) (A + 144 <= d4 \/ d4 + 64 <= A) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M26 (m_vmmaps model26) ->
  (* [comment removed for export] *) model_ok model26 ->
  (* [comment removed for export] *) model_but_vm model model26 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M26 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx25 R26 140348 M26 model26) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R26_2 R26_3 R26_4 R26_8 R26_9 R26_18 R26_19 R26_20 R26_21 R26_22 R26_23 R26_24 R26_25 R26_26 R26_27 c26_Sm56 c26_Sm64 c26_Sm72 c26_Sm80 c26_Sm88 c26_Sm96 c26_Sm104 c26_Sm112 c26_Sm120 c26_Sm128 c26_Sm136 c26_Sm144 c26_Sm152 c26_Sm8 c26_Sm16 c26_Sm280w1 c26_Sm248w1 c26_Sm216w1 c26_Sm192 c26_Sm200 c26_Sm184w1 c26_Sm160 c26_Sm168 c26_Sm48w1 c26_Om128z8 c26_Om80z12 c26_Op0 c26_Op8 c26_Fp24 c26_Fp32 c26_Fp40 c26_Fp48 c26_Fp56 c26_Fp64w1 c26_Fp65w1 c26_Fp16w4 c26_Fp8 c26_Fp0 c26_Om8 c26_Om40 c26_Om48 c26_Om56 c26_Om64 c26_Om68w4 c26_Om16 c26_Om120 c26_Om24 c26_Om32 c26_Om88 c26_Om104 c26_Om112 c26_Om96 ES26 DEF26 DEFref_26 DEFA_26 DEFd4_26 BR_ref BR_A BR_d4 AP_ref_A AP_ref_d4 AP_A_d4 FRSH_ref FRSH_A HH26 MOK26 MBV26 HQ26 KE.
  pose proof MOK26 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES26 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  set (u26_10 := U R26 10). assert (Wu26_10: 0 <= u26_10 < 2 ^ 64) by (unfold u26_10, U; apply wrange).
  assert (R26_10: getr R26 (reg 10) = Z_to_bv 64 u26_10) by (unfold u26_10, U; symmetry; apply lit_of_word). clearbody u26_10.
  pose proof ES26 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M26 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p5b_conc fx25 R26 M26 (S - 896) (A + 128) u26_10 fb184 d4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx27 & R27 & M27 & MS27 & K27 & R27_1 & R27_2 & R27_10 & R27_11 & FR27 & GR27).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu26_10. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb184. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF26 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF26); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF26 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF26); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_26 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_26); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_26 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_26); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d4 B1_d4 B3_d4 B4_d4 AP_A_d4. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb184. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite lor1_land254_bit1 by (assumption || kl). first [exact c26_Sm184w1 | cellfix c26_Sm184w1]. }
  { (* [comment removed for export] *) first [exact c26_Sm160 | cellfix c26_Sm160]. }
  { (* [comment removed for export] *) first [exact c26_Sm168 | cellfix c26_Sm168]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS27.
  (* [comment removed for export] *)
  assert (AG27: forall a k, ((a + k <= (S - 416) \/ (S - 352) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M26 M27 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR27; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R27_1n: getr R27 (reg 1) = Z_to_bv 64 140388) by (rewrite R27_1; f_equal; ring). clear R27_1. rename R27_1n into R27_1.
  assert (R27_2n: getr R27 (reg 2) = Z_to_bv 64 (S - 352)) by (rewrite R27_2; f_equal; ring). clear R27_2. rename R27_2n into R27_2.
  assert (R27_3: getr R27 (reg 3) = Z_to_bv 64 67584) by (kin K27 3%nat; exact R26_3).
  assert (R27_4: getr R27 (reg 4) = Z_to_bv 64 459832) by (kin K27 4%nat; exact R26_4).
  assert (R27_8: getr R27 (reg 8) = Z_to_bv 64 (A + 96)) by (kin K27 8%nat; exact R26_8).
  assert (R27_9: getr R27 (reg 9) = Z_to_bv 64 (S - 48)) by (kin K27 9%nat; exact R26_9).
  assert (R27_10n: getr R27 (reg 10) = Z_to_bv 64 d4) by (rewrite R27_10; f_equal; ring). clear R27_10. rename R27_10n into R27_10.
  assert (R27_11n: getr R27 (reg 11) = Z_to_bv 64 64) by (rewrite R27_11; f_equal; ring). clear R27_11. rename R27_11n into R27_11.
  assert (R27_18: getr R27 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K27 18%nat; exact R26_18).
  assert (R27_19: getr R27 (reg 19) = Z_to_bv 64 w504) by (kin K27 19%nat; exact R26_19).
  assert (R27_20: getr R27 (reg 20) = Z_to_bv 64 w512) by (kin K27 20%nat; exact R26_20).
  assert (R27_21: getr R27 (reg 21) = Z_to_bv 64 w520) by (kin K27 21%nat; exact R26_21).
  assert (R27_22: getr R27 (reg 22) = Z_to_bv 64 w528) by (kin K27 22%nat; exact R26_22).
  assert (R27_23: getr R27 (reg 23) = Z_to_bv 64 w536) by (kin K27 23%nat; exact R26_23).
  assert (R27_24: getr R27 (reg 24) = Z_to_bv 64 w544) by (kin K27 24%nat; exact R26_24).
  assert (R27_25: getr R27 (reg 25) = Z_to_bv 64 w552) by (kin K27 25%nat; exact R26_25).
  assert (R27_26: getr R27 (reg 26) = Z_to_bv 64 w560) by (kin K27 26%nat; exact R26_26).
  assert (R27_27: getr R27 (reg 27) = Z_to_bv 64 w568) by (kin K27 27%nat; exact R26_27).
  assert (c27_Sm56: L5.u64_at RSEGS M27 (S - 56) 138528) by (clear - AG27 c26_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm56]).
  assert (c27_Sm64: L5.u64_at RSEGS M27 (S - 64) (S + 64)) by (clear - AG27 c26_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm64]).
  assert (c27_Sm72: L5.u64_at RSEGS M27 (S - 72) (U R0 9)) by (clear - AG27 c26_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm72]).
  assert (c27_Sm80: L5.u64_at RSEGS M27 (S - 80) (U R0 18)) by (clear - AG27 c26_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm80]).
  assert (c27_Sm88: L5.u64_at RSEGS M27 (S - 88) (U R0 19)) by (clear - AG27 c26_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm88]).
  assert (c27_Sm96: L5.u64_at RSEGS M27 (S - 96) (U R0 20)) by (clear - AG27 c26_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm96]).
  assert (c27_Sm104: L5.u64_at RSEGS M27 (S - 104) (U R0 21)) by (clear - AG27 c26_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm104]).
  assert (c27_Sm112: L5.u64_at RSEGS M27 (S - 112) (U R0 22)) by (clear - AG27 c26_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm112]).
  assert (c27_Sm120: L5.u64_at RSEGS M27 (S - 120) (U R0 23)) by (clear - AG27 c26_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm120]).
  assert (c27_Sm128: L5.u64_at RSEGS M27 (S - 128) (U R0 24)) by (clear - AG27 c26_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm128]).
  assert (c27_Sm136: L5.u64_at RSEGS M27 (S - 136) (U R0 25)) by (clear - AG27 c26_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm136]).
  assert (c27_Sm144: L5.u64_at RSEGS M27 (S - 144) (U R0 26)) by (clear - AG27 c26_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm144]).
  assert (c27_Sm152: L5.u64_at RSEGS M27 (S - 152) (U R0 27)) by (clear - AG27 c26_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm152]).
  assert (c27_Sm8: L5.u64_at RSEGS M27 (S - 8) 132608) by (clear - AG27 c26_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm8]).
  assert (c27_Sm16: L5.u64_at RSEGS M27 (S - 16) (U R0 8)) by (clear - AG27 c26_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm16]).
  assert (c27_Sm280w1: L5.u8_at RSEGS M27 (S - 280) fb280) by (clear - AG27 c26_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Sm280w1]).
  assert (c27_Sm248w1: L5.u8_at RSEGS M27 (S - 248) fb248) by (clear - AG27 c26_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Sm248w1]).
  assert (c27_Sm216w1: L5.u8_at RSEGS M27 (S - 216) fb216) by (clear - AG27 c26_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Sm216w1]).
  assert (c27_Sm192: L5.u64_at RSEGS M27 (S - 192) d3) by (clear - AG27 c26_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm192]).
  assert (c27_Sm200: L5.u64_at RSEGS M27 (S - 200) 8) by (clear - AG27 c26_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm200]).
  assert (c27_Sm184w1: L5.u8_at RSEGS M27 (S - 184) fb184) by (clear - AG27 c26_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Sm184w1]).
  assert (c27_Sm160: L5.u64_at RSEGS M27 (S - 160) d4) by (clear - AG27 c26_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm160]).
  assert (c27_Sm168: L5.u64_at RSEGS M27 (S - 168) 8) by (clear - AG27 c26_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Sm168]).
  assert (c27_Sm48w1: L5.u8_at RSEGS M27 (S - 48) fb48) by (clear - AG27 c26_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Sm48w1]).
  assert (c27_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M27 (A + i) 0)) by (clear - AG27 c26_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | apply c26_Om128z8; exact Hi]).
  assert (c27_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M27 ((A + 48) + i) 0)) by (clear - AG27 c26_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | apply c26_Om80z12; exact Hi]).
  assert (c27_Op0: L5.u64_at RSEGS M27 (A + 128) 373272) by (clear - AG27 c26_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Op0]).
  assert (c27_Op8: L5.u64_at RSEGS M27 (A + 136) (ref + 24)) by (clear - AG27 c26_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Op8]).
  assert (c27_Fp24: L5.u64_at RSEGS M27 (ref + 24) 8028075845441778529) by (clear - AG27 c26_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp24]).
  assert (c27_Fp32: L5.u64_at RSEGS M27 (ref + 32) 7863351059373564014) by (clear - AG27 c26_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp32]).
  assert (c27_Fp40: L5.u64_at RSEGS M27 (ref + 40) 2838809733452757089) by (clear - AG27 c26_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp40]).
  assert (c27_Fp48: L5.u64_at RSEGS M27 (ref + 48) 2334102023183623712) by (clear - AG27 c26_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp48]).
  assert (c27_Fp56: L5.u64_at RSEGS M27 (ref + 56) 4188416081412519009) by (clear - AG27 c26_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp56]).
  assert (c27_Fp64w1: L5.u8_at RSEGS M27 (ref + 64) 48) by (clear - AG27 c26_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Fp64w1]).
  assert (c27_Fp65w1: L5.u8_at RSEGS M27 (ref + 65) 0) by (clear - AG27 c26_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M26 M27 _ _ _ (AG27 _ 1)); [lia | exact c26_Fp65w1]).
  assert (c27_Fp16w4: L5.u32_at RSEGS M27 (ref + 16) 0) by (clear - AG27 c26_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M26 M27 _ _ _ (AG27 _ 4)); [lia | exact c26_Fp16w4]).
  assert (c27_Fp8: L5.u64_at RSEGS M27 (ref + 8) 41) by (clear - AG27 c26_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp8]).
  assert (c27_Fp0: L5.u64_at RSEGS M27 ref 41) by (clear - AG27 c26_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Fp0]).
  assert (c27_Om8: L5.u64_at RSEGS M27 (A + 120) S) by (clear - AG27 c26_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om8]).
  assert (c27_Om40: L5.u64_at RSEGS M27 (A + 88) (A + 128)) by (clear - AG27 c26_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om40]).
  assert (c27_Om48: L5.u64_at RSEGS M27 (A + 80) 133016) by (clear - AG27 c26_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om48]).
  assert (c27_Om56: L5.u64_at RSEGS M27 (A + 72) 91560) by (clear - AG27 c26_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om56]).
  assert (c27_Om64: L5.u64_at RSEGS M27 (A + 64) 91699) by (clear - AG27 c26_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om64]).
  assert (c27_Om68w4: L5.u32_at RSEGS M27 (A + 60) 1) by (clear - AG27 c26_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M26 M27 _ _ _ (AG27 _ 4)); [lia | exact c26_Om68w4]).
  assert (c27_Om16: L5.u64_at RSEGS M27 (A + 112) 0) by (clear - AG27 c26_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om16]).
  assert (c27_Om120: L5.u64_at RSEGS M27 (A + 8) 1) by (clear - AG27 c26_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om120]).
  assert (c27_Om24: L5.u64_at RSEGS M27 (A + 104) 257624) by (clear - AG27 c26_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om24]).
  assert (c27_Om32: L5.u64_at RSEGS M27 (A + 96) 4849336966747728640) by (clear - AG27 c26_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om32]).
  assert (c27_Om88: L5.u64_at RSEGS M27 (A + 40) 142700) by (clear - AG27 c26_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om88]).
  assert (c27_Om104: L5.u64_at RSEGS M27 (A + 24) 253816) by (clear - AG27 c26_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om104]).
  assert (c27_Om112: L5.u64_at RSEGS M27 (A + 16) 373232) by (clear - AG27 c26_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om112]).
  assert (c27_Om96: L5.u64_at RSEGS M27 (A + 32) 142968) by (clear - AG27 c26_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M26 M27 _ _ _ (AG27 _ 8)); [lia | exact c26_Om96]).
  assert (STAT27: forall a, stat_rd av a -> M27 (Z_to_bv 64 a) = M26 (Z_to_bv 64 a)).
  { clear - FR27 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR27; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M26 M27 gd av uid rnd canary hw ES26 STAT27) as ES27.
  assert (DEF27: L5.defined M27 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR27 | exact DEF26]).
  assert (DEFref_27: L5.defined M27 ref 66) by (eapply L5.defined_grows; [exact GR27 | exact DEFref_26]).
  assert (DEFA_27: L5.defined M27 A 144) by (eapply L5.defined_grows; [exact GR27 | exact DEFA_26]).
  assert (DEFd4_27: L5.defined M27 d4 64) by (eapply L5.defined_grows; [exact GR27 | exact DEFd4_26]).
  assert (HH27: hi_heap HI ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M27 (m_vmmaps model26)).
  { clear - HH26 GR27 FR27 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH26. lia. 2: exact GR27. intros a Ha.
    destruct (in_dec (S - 416) (S - 352) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR27; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ27: L5C.hpres L LB1 S 10240 XSF M M27).
  { clear - LBWF HQ26 FR27 GR27 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M26 M27 [((S - 416), 64)]). exact LBWF. lia. exact HQ26.
    { intros x Hx. apply FR27; intros Hin.
        apply (Hx ((S - 416), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR27.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG27 FR27 MS27. try clear STAT27. try clear K26.
  try clear c26_Sm56. try clear c26_Sm64. try clear c26_Sm72. try clear c26_Sm80. try clear c26_Sm88. try clear c26_Sm96. try clear c26_Sm104. try clear c26_Sm112. try clear c26_Sm120. try clear c26_Sm128. try clear c26_Sm136. try clear c26_Sm144. try clear c26_Sm152. try clear c26_Sm8. try clear c26_Sm16. try clear c26_Sm280w1. try clear c26_Sm248w1. try clear c26_Sm216w1. try clear c26_Sm192. try clear c26_Sm200. try clear c26_Sm184w1. try clear c26_Sm160. try clear c26_Sm168. try clear c26_Sm48w1. try clear c26_Om128z8. try clear c26_Om80z12. try clear c26_Op0. try clear c26_Op8. try clear c26_Fp24. try clear c26_Fp32. try clear c26_Fp40. try clear c26_Fp48. try clear c26_Fp56. try clear c26_Fp64w1. try clear c26_Fp65w1. try clear c26_Fp16w4. try clear c26_Fp8. try clear c26_Fp0. try clear c26_Om8. try clear c26_Om40. try clear c26_Om48. try clear c26_Om56. try clear c26_Om64. try clear c26_Om68w4. try clear c26_Om16. try clear c26_Om120. try clear c26_Om24. try clear c26_Om32. try clear c26_Om88. try clear c26_Om104. try clear c26_Om112. try clear c26_Om96. try clear R26_2. try clear R26_3. try clear R26_4. try clear R26_8. try clear R26_9. try clear R26_18. try clear R26_19. try clear R26_20. try clear R26_21. try clear R26_22. try clear R26_23. try clear R26_24. try clear R26_25. try clear R26_26. try clear R26_27. try clear R26_10. try clear DEF26. try clear HH26. try clear HQ26. try clear ES26. try clear DEFref_26. try clear DEFA_26. try clear DEFd4_26.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx27 R27 M27 model26 ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) d4 64 K) as HC.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH27.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - right; right; left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R27_10.
  - rewrite L5CoreKit.L5K.rl4. exact R27_4.
  - rewrite L5CoreKit.L5K.rl1, R27_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R27_2 A16 DEF27 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R27_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-22) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M27 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF27. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R28 M28 model28 RP28 [PRES28 _] MBVn HH28.
    rewrite L5CoreKit.L5K.rl1, R27_1.
    cbn [lb_remove fst app] in PRES28, HH28.
    rewrite (proj2 (Z.eqb_neq ref d4) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref B0_d4 B1_d4 B3_d4 B4_d4 AP_ref_d4)) in PRES28, HH28.
    rewrite (proj2 (Z.eqb_neq A d4) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d4 B1_d4 B3_d4 B4_d4 AP_A_d4)) in PRES28, HH28.
    rewrite Z.eqb_refl in PRES28, HH28.
    rewrite L5CoreKit.L5K.rl2, R27_2, BG.unsigned_lit in PRES28 by (kl SLO SHI STOP).
    match type of PRES28 with heap_pres_core _ _ ?x _ _ => replace x with (S - 352) in PRES28 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((ref, 66) :: (A, 144) :: LB1) (S - 352) M27 M28 PRES28) as HP28. rewrite (ly_stack L LY) in HP28. unfold HEAP_STACK in HP28.
    assert (AGS28: forall a k, ((S - 352) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M27 M28 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP28 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP28. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB28_ref: L5C.agree_on M27 M28 ref 66).
    { clear - HP28 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP28. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB28_A: L5C.agree_on M27 M28 A 144).
    { clear - HP28 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP28. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT28: forall a, stat_rd av a -> M28 (Z_to_bv 64 a) = M27 (Z_to_bv 64 a)).
    { clear - HP28 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((ref, 66) :: (A, 144) :: LB1) (S - 352) 8224 [] M27 M28 HP28). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (statics_landed_keep M27 M28 gd av uid rnd canary hw ES27 STAT28) as ES28.
    assert (DEF28: L5.defined M28 (S - 10240) 10240).
    { clear - HP28 DEF27 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((ref, 66) :: (A, 144) :: LB1) (S - 352) 8224 [] M27 M28). exact HP28. lia. lia. lia. lia. exact DEF27. }
    assert (DEFref_28: L5.defined M28 ref 66) by (eapply (L5C.defined_agree M27 M28); [exact AGB28_ref | exact DEFref_27]).
    assert (DEFA_28: L5.defined M28 A 144) by (eapply (L5C.defined_agree M27 M28); [exact AGB28_A | exact DEFA_27]).
    assert (MOK28: model_ok model28).
    { destruct MOK26 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK28 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV26 MBVn) as MBV28. clear MBVn MBV26.
    assert (RPi28: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R28 (reg i) = getr R27 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R27 R28 i RP28). exact Hi. }
    assert (R28_2: getr R28 (reg 2) = Z_to_bv 64 (S - 352)) by (rewrite (RPi28 2%nat) by inl; exact R27_2).
    assert (R28_3: getr R28 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi28 3%nat) by inl; exact R27_3).
    assert (R28_4: getr R28 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi28 4%nat) by inl; exact R27_4).
    assert (R28_8: getr R28 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite (RPi28 8%nat) by inl; exact R27_8).
    assert (R28_9: getr R28 (reg 9) = Z_to_bv 64 (S - 48)) by (rewrite (RPi28 9%nat) by inl; exact R27_9).
    assert (R28_18: getr R28 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite (RPi28 18%nat) by inl; exact R27_18).
    assert (R28_19: getr R28 (reg 19) = Z_to_bv 64 w504) by (rewrite (RPi28 19%nat) by inl; exact R27_19).
    assert (R28_20: getr R28 (reg 20) = Z_to_bv 64 w512) by (rewrite (RPi28 20%nat) by inl; exact R27_20).
    assert (R28_21: getr R28 (reg 21) = Z_to_bv 64 w520) by (rewrite (RPi28 21%nat) by inl; exact R27_21).
    assert (R28_22: getr R28 (reg 22) = Z_to_bv 64 w528) by (rewrite (RPi28 22%nat) by inl; exact R27_22).
    assert (R28_23: getr R28 (reg 23) = Z_to_bv 64 w536) by (rewrite (RPi28 23%nat) by inl; exact R27_23).
    assert (R28_24: getr R28 (reg 24) = Z_to_bv 64 w544) by (rewrite (RPi28 24%nat) by inl; exact R27_24).
    assert (R28_25: getr R28 (reg 25) = Z_to_bv 64 w552) by (rewrite (RPi28 25%nat) by inl; exact R27_25).
    assert (R28_26: getr R28 (reg 26) = Z_to_bv 64 w560) by (rewrite (RPi28 26%nat) by inl; exact R27_26).
    assert (R28_27: getr R28 (reg 27) = Z_to_bv 64 w568) by (rewrite (RPi28 27%nat) by inl; exact R27_27).
    assert (c28_Sm56: L5.u64_at RSEGS M28 (S - 56) 138528) by (clear - AGS28 c27_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm56]).
    assert (c28_Sm64: L5.u64_at RSEGS M28 (S - 64) (S + 64)) by (clear - AGS28 c27_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm64]).
    assert (c28_Sm72: L5.u64_at RSEGS M28 (S - 72) (U R0 9)) by (clear - AGS28 c27_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm72]).
    assert (c28_Sm80: L5.u64_at RSEGS M28 (S - 80) (U R0 18)) by (clear - AGS28 c27_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm80]).
    assert (c28_Sm88: L5.u64_at RSEGS M28 (S - 88) (U R0 19)) by (clear - AGS28 c27_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm88]).
    assert (c28_Sm96: L5.u64_at RSEGS M28 (S - 96) (U R0 20)) by (clear - AGS28 c27_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm96]).
    assert (c28_Sm104: L5.u64_at RSEGS M28 (S - 104) (U R0 21)) by (clear - AGS28 c27_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm104]).
    assert (c28_Sm112: L5.u64_at RSEGS M28 (S - 112) (U R0 22)) by (clear - AGS28 c27_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm112]).
    assert (c28_Sm120: L5.u64_at RSEGS M28 (S - 120) (U R0 23)) by (clear - AGS28 c27_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm120]).
    assert (c28_Sm128: L5.u64_at RSEGS M28 (S - 128) (U R0 24)) by (clear - AGS28 c27_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm128]).
    assert (c28_Sm136: L5.u64_at RSEGS M28 (S - 136) (U R0 25)) by (clear - AGS28 c27_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm136]).
    assert (c28_Sm144: L5.u64_at RSEGS M28 (S - 144) (U R0 26)) by (clear - AGS28 c27_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm144]).
    assert (c28_Sm152: L5.u64_at RSEGS M28 (S - 152) (U R0 27)) by (clear - AGS28 c27_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm152]).
    assert (c28_Sm8: L5.u64_at RSEGS M28 (S - 8) 132608) by (clear - AGS28 c27_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm8]).
    assert (c28_Sm16: L5.u64_at RSEGS M28 (S - 16) (U R0 8)) by (clear - AGS28 c27_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm16]).
    assert (c28_Sm280w1: L5.u8_at RSEGS M28 (S - 280) fb280) by (clear - AGS28 c27_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M27 M28 _ _ _ (AGS28 _ 1)); [lia | exact c27_Sm280w1]).
    assert (c28_Sm248w1: L5.u8_at RSEGS M28 (S - 248) fb248) by (clear - AGS28 c27_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M27 M28 _ _ _ (AGS28 _ 1)); [lia | exact c27_Sm248w1]).
    assert (c28_Sm216w1: L5.u8_at RSEGS M28 (S - 216) fb216) by (clear - AGS28 c27_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M27 M28 _ _ _ (AGS28 _ 1)); [lia | exact c27_Sm216w1]).
    assert (c28_Sm192: L5.u64_at RSEGS M28 (S - 192) d3) by (clear - AGS28 c27_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm192]).
    assert (c28_Sm200: L5.u64_at RSEGS M28 (S - 200) 8) by (clear - AGS28 c27_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm200]).
    assert (c28_Sm184w1: L5.u8_at RSEGS M28 (S - 184) fb184) by (clear - AGS28 c27_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M27 M28 _ _ _ (AGS28 _ 1)); [lia | exact c27_Sm184w1]).
    assert (c28_Sm160: L5.u64_at RSEGS M28 (S - 160) d4) by (clear - AGS28 c27_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm160]).
    assert (c28_Sm168: L5.u64_at RSEGS M28 (S - 168) 8) by (clear - AGS28 c27_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M27 M28 _ _ _ (AGS28 _ 8)); [lia | exact c27_Sm168]).
    assert (c28_Sm48w1: L5.u8_at RSEGS M28 (S - 48) fb48) by (clear - AGS28 c27_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M27 M28 _ _ _ (AGS28 _ 1)); [lia | exact c27_Sm48w1]).
    assert (c28_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M28 (A + i) 0)) by (clear - AGB28_A c27_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB28_A); [lia | apply c27_Om128z8; exact Hi]).
    assert (c28_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M28 ((A + 48) + i) 0)) by (clear - AGB28_A c27_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB28_A); [lia | apply c27_Om80z12; exact Hi]).
    assert (c28_Op0: L5.u64_at RSEGS M28 (A + 128) 373272) by (clear - AGB28_A c27_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Op0]).
    assert (c28_Op8: L5.u64_at RSEGS M28 (A + 136) (ref + 24)) by (clear - AGB28_A c27_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Op8]).
    assert (c28_Fp24: L5.u64_at RSEGS M28 (ref + 24) 8028075845441778529) by (clear - AGB28_ref c27_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp24]).
    assert (c28_Fp32: L5.u64_at RSEGS M28 (ref + 32) 7863351059373564014) by (clear - AGB28_ref c27_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp32]).
    assert (c28_Fp40: L5.u64_at RSEGS M28 (ref + 40) 2838809733452757089) by (clear - AGB28_ref c27_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp40]).
    assert (c28_Fp48: L5.u64_at RSEGS M28 (ref + 48) 2334102023183623712) by (clear - AGB28_ref c27_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp48]).
    assert (c28_Fp56: L5.u64_at RSEGS M28 (ref + 56) 4188416081412519009) by (clear - AGB28_ref c27_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp56]).
    assert (c28_Fp64w1: L5.u8_at RSEGS M28 (ref + 64) 48) by (clear - AGB28_ref c27_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp64w1]).
    assert (c28_Fp65w1: L5.u8_at RSEGS M28 (ref + 65) 0) by (clear - AGB28_ref c27_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp65w1]).
    assert (c28_Fp16w4: L5.u32_at RSEGS M28 (ref + 16) 0) by (clear - AGB28_ref c27_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb32 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp16w4]).
    assert (c28_Fp8: L5.u64_at RSEGS M28 (ref + 8) 41) by (clear - AGB28_ref c27_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp8]).
    assert (c28_Fp0: L5.u64_at RSEGS M28 ref 41) by (clear - AGB28_ref c27_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB28_ref); [lia | exact c27_Fp0]).
    assert (c28_Om8: L5.u64_at RSEGS M28 (A + 120) S) by (clear - AGB28_A c27_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om8]).
    assert (c28_Om40: L5.u64_at RSEGS M28 (A + 88) (A + 128)) by (clear - AGB28_A c27_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om40]).
    assert (c28_Om48: L5.u64_at RSEGS M28 (A + 80) 133016) by (clear - AGB28_A c27_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om48]).
    assert (c28_Om56: L5.u64_at RSEGS M28 (A + 72) 91560) by (clear - AGB28_A c27_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om56]).
    assert (c28_Om64: L5.u64_at RSEGS M28 (A + 64) 91699) by (clear - AGB28_A c27_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om64]).
    assert (c28_Om68w4: L5.u32_at RSEGS M28 (A + 60) 1) by (clear - AGB28_A c27_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb32 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om68w4]).
    assert (c28_Om16: L5.u64_at RSEGS M28 (A + 112) 0) by (clear - AGB28_A c27_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om16]).
    assert (c28_Om120: L5.u64_at RSEGS M28 (A + 8) 1) by (clear - AGB28_A c27_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om120]).
    assert (c28_Om24: L5.u64_at RSEGS M28 (A + 104) 257624) by (clear - AGB28_A c27_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om24]).
    assert (c28_Om32: L5.u64_at RSEGS M28 (A + 96) 4849336966747728640) by (clear - AGB28_A c27_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om32]).
    assert (c28_Om88: L5.u64_at RSEGS M28 (A + 40) 142700) by (clear - AGB28_A c27_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om88]).
    assert (c28_Om104: L5.u64_at RSEGS M28 (A + 24) 253816) by (clear - AGB28_A c27_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om104]).
    assert (c28_Om112: L5.u64_at RSEGS M28 (A + 16) 373232) by (clear - AGB28_A c27_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om112]).
    assert (c28_Om96: L5.u64_at RSEGS M28 (A + 32) 142968) by (clear - AGB28_A c27_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB28_A); [lia | exact c27_Om96]).
    assert (HQ28: L5C.hpres L LB1 S 10240 XSF M M28).
    { clear - LBWF HQ27 HP28 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((ref, 66) :: (A, 144) :: LB1) S 10240 XSF (S - 352) 8224 [] M M27 M28). exact LBWF. lia. lia. exact HQ27. exact HP28. intros bb Hbb; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS28 STAT28 PRES28 RP28 RPi28 HP28 AGB28_ref AGB28_A.
    try clear c27_Sm56 c27_Sm64 c27_Sm72 c27_Sm80 c27_Sm88 c27_Sm96 c27_Sm104 c27_Sm112 c27_Sm120 c27_Sm128 c27_Sm136 c27_Sm144 c27_Sm152 c27_Sm8 c27_Sm16 c27_Sm280w1 c27_Sm248w1 c27_Sm216w1 c27_Sm192 c27_Sm200 c27_Sm184w1 c27_Sm160 c27_Sm168 c27_Sm48w1 c27_Om128z8 c27_Om80z12 c27_Op0 c27_Op8 c27_Fp24 c27_Fp32 c27_Fp40 c27_Fp48 c27_Fp56 c27_Fp64w1 c27_Fp65w1 c27_Fp16w4 c27_Fp8 c27_Fp0 c27_Om8 c27_Om40 c27_Om48 c27_Om56 c27_Om64 c27_Om68w4 c27_Om16 c27_Om120 c27_Om24 c27_Om32 c27_Om88 c27_Om104 c27_Om112 c27_Om96 R27_1 R27_2 R27_3 R27_4 R27_8 R27_9 R27_10 R27_11 R27_18 R27_19 R27_20 R27_21 R27_22 R27_23 R27_24 R27_25 R27_26 R27_27 DEF27 HH27 HQ27 ES27 K27 DEFref_27 DEFA_27 DEFd4_27.
    eapply (seg16 fx27 R0 R R28 M M28 model model28 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R28_2 R28_3 R28_4 R28_8 R28_9 R28_18 R28_19 R28_20 R28_21 R28_22 R28_23 R28_24 R28_25 R28_26 R28_27 c28_Sm56 c28_Sm64 c28_Sm72 c28_Sm80 c28_Sm88 c28_Sm96 c28_Sm104 c28_Sm112 c28_Sm120 c28_Sm128 c28_Sm136 c28_Sm144 c28_Sm152 c28_Sm8 c28_Sm16 c28_Sm280w1 c28_Sm248w1 c28_Sm216w1 c28_Sm192 c28_Sm200 c28_Sm184w1 c28_Sm160 c28_Sm168 c28_Sm48w1 c28_Om128z8 c28_Om80z12 c28_Op0 c28_Op8 c28_Fp24 c28_Fp32 c28_Fp40 c28_Fp48 c28_Fp56 c28_Fp64w1 c28_Fp65w1 c28_Fp16w4 c28_Fp8 c28_Fp0 c28_Om8 c28_Om40 c28_Om48 c28_Om56 c28_Om64 c28_Om68w4 c28_Om16 c28_Om120 c28_Om24 c28_Om32 c28_Om88 c28_Om104 c28_Om112 c28_Om96 ES28 DEF28 DEFref_28 DEFA_28 BR_ref BR_A AP_ref_A FRSH_ref FRSH_A HH28 MOK28 MBV28 HQ28 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S15.
