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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S17.
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

Lemma seg17 (fx30 : FPState) (R0 R R30 : bvmap 5 word) (M M30 : word -> option byte) (model model28 : Model) (K : TSet)
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
  (* [comment removed for export] *) getr R30 (reg 1) = Z_to_bv 64 138580 ->
  (* [comment removed for export] *) getr R30 (reg 2) = Z_to_bv 64 (S - 48) ->
  (* [comment removed for export] *) getr R30 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R30 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R30 (reg 8) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R30 (reg 9) = Z_to_bv 64 (U R0 9) ->
  (* [comment removed for export] *) getr R30 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R30 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R30 (reg 18) = Z_to_bv 64 (U R0 18) ->
  (* [comment removed for export] *) getr R30 (reg 19) = Z_to_bv 64 (U R0 19) ->
  (* [comment removed for export] *) getr R30 (reg 20) = Z_to_bv 64 (U R0 20) ->
  (* [comment removed for export] *) getr R30 (reg 21) = Z_to_bv 64 (U R0 21) ->
  (* [comment removed for export] *) getr R30 (reg 22) = Z_to_bv 64 (U R0 22) ->
  (* [comment removed for export] *) getr R30 (reg 23) = Z_to_bv 64 (U R0 23) ->
  (* [comment removed for export] *) getr R30 (reg 24) = Z_to_bv 64 (U R0 24) ->
  (* [comment removed for export] *) getr R30 (reg 25) = Z_to_bv 64 (U R0 25) ->
  (* [comment removed for export] *) getr R30 (reg 26) = Z_to_bv 64 (U R0 26) ->
  (* [comment removed for export] *) getr R30 (reg 27) = Z_to_bv 64 (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M30 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M30 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M30 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M30 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M30 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M30 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M30 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M30 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M30 ref 66 ->
  (* [comment removed for export] *) L5.defined M30 A 144 ->
  (* [comment removed for export] *) block_range L ref 66 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) (ref + 66 <= A \/ A + 144 <= ref) ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 ref 66 ->
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M30 (m_vmmaps model28) ->
  (* [comment removed for export] *) model_ok model28 ->
  (* [comment removed for export] *) model_but_vm model model28 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M30 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx30 R30 138580 M30 model28) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R30_1 R30_2 R30_3 R30_4 R30_8 R30_9 R30_10 R30_11 R30_18 R30_19 R30_20 R30_21 R30_22 R30_23 R30_24 R30_25 R30_26 R30_27 c30_Sm56 c30_Sm64 c30_Sm72 c30_Sm80 c30_Sm88 c30_Sm96 c30_Sm104 c30_Sm112 c30_Sm120 c30_Sm128 c30_Sm136 c30_Sm144 c30_Sm152 c30_Sm8 c30_Sm16 c30_Sm280w1 c30_Sm248w1 c30_Sm216w1 c30_Sm192 c30_Sm200 c30_Sm184w1 c30_Sm160 c30_Sm168 c30_Sm48w1 c30_Om128z8 c30_Om80z12 c30_Op0 c30_Op8 c30_Fp24 c30_Fp32 c30_Fp40 c30_Fp48 c30_Fp56 c30_Fp64w1 c30_Fp65w1 c30_Fp16w4 c30_Fp8 c30_Fp0 c30_Om8 c30_Om40 c30_Om48 c30_Om56 c30_Om64 c30_Om68w4 c30_Om16 c30_Om120 c30_Om24 c30_Om32 c30_Om88 c30_Om104 c30_Om112 c30_Om96 ES30 DEF30 DEFref_30 DEFA_30 BR_ref BR_A AP_ref_A FRSH_ref FRSH_A HH30 MOK28 MBV28 HQ30 KE.
  pose proof MOK28 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof ES30 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES30 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M30 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p6_conc fx30 R30 M30 (S - 896) (A + 128) fb48 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx31 & R31 & M31 & MS31 & K31 & R31_2 & R31_8 & R31_10 & R31_11 & FR31 & GR31).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb48. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF30 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF30); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF30 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF30); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_30 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_30); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_30 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_30); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb48. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c30_Sm48w1 | cellfix c30_Sm48w1]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS31.
  (* [comment removed for export] *)
  assert (AG31: forall a k, ((a + k <= (S - 112) \/ (S - 48) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M30 M31 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR31; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R31_1: getr R31 (reg 1) = Z_to_bv 64 138580) by (kin K31 1%nat; exact R30_1).
  assert (R31_2n: getr R31 (reg 2) = Z_to_bv 64 (S - 48)) by (rewrite R31_2; f_equal; ring). clear R31_2. rename R31_2n into R31_2.
  assert (R31_3: getr R31 (reg 3) = Z_to_bv 64 67584) by (kin K31 3%nat; exact R30_3).
  assert (R31_4: getr R31 (reg 4) = Z_to_bv 64 459832) by (kin K31 4%nat; exact R30_4).
  assert (R31_8n: getr R31 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R31_8; f_equal; ring). clear R31_8. rename R31_8n into R31_8.
  assert (R31_9: getr R31 (reg 9) = Z_to_bv 64 (U R0 9)) by (kin K31 9%nat; exact R30_9).
  assert (R31_10n: getr R31 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R31_10; f_equal; ring). clear R31_10. rename R31_10n into R31_10.
  assert (R31_11n: getr R31 (reg 11) = Z_to_bv 64 0) by (rewrite R31_11; f_equal; ring). clear R31_11. rename R31_11n into R31_11.
  assert (R31_18: getr R31 (reg 18) = Z_to_bv 64 (U R0 18)) by (kin K31 18%nat; exact R30_18).
  assert (R31_19: getr R31 (reg 19) = Z_to_bv 64 (U R0 19)) by (kin K31 19%nat; exact R30_19).
  assert (R31_20: getr R31 (reg 20) = Z_to_bv 64 (U R0 20)) by (kin K31 20%nat; exact R30_20).
  assert (R31_21: getr R31 (reg 21) = Z_to_bv 64 (U R0 21)) by (kin K31 21%nat; exact R30_21).
  assert (R31_22: getr R31 (reg 22) = Z_to_bv 64 (U R0 22)) by (kin K31 22%nat; exact R30_22).
  assert (R31_23: getr R31 (reg 23) = Z_to_bv 64 (U R0 23)) by (kin K31 23%nat; exact R30_23).
  assert (R31_24: getr R31 (reg 24) = Z_to_bv 64 (U R0 24)) by (kin K31 24%nat; exact R30_24).
  assert (R31_25: getr R31 (reg 25) = Z_to_bv 64 (U R0 25)) by (kin K31 25%nat; exact R30_25).
  assert (R31_26: getr R31 (reg 26) = Z_to_bv 64 (U R0 26)) by (kin K31 26%nat; exact R30_26).
  assert (R31_27: getr R31 (reg 27) = Z_to_bv 64 (U R0 27)) by (kin K31 27%nat; exact R30_27).
  assert (c31_Sm120: L5.u64_at RSEGS M31 (S - 120) (U R0 23)) by (clear - AG31 c30_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm120]).
  assert (c31_Sm128: L5.u64_at RSEGS M31 (S - 128) (U R0 24)) by (clear - AG31 c30_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm128]).
  assert (c31_Sm136: L5.u64_at RSEGS M31 (S - 136) (U R0 25)) by (clear - AG31 c30_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm136]).
  assert (c31_Sm144: L5.u64_at RSEGS M31 (S - 144) (U R0 26)) by (clear - AG31 c30_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm144]).
  assert (c31_Sm152: L5.u64_at RSEGS M31 (S - 152) (U R0 27)) by (clear - AG31 c30_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm152]).
  assert (c31_Sm8: L5.u64_at RSEGS M31 (S - 8) 132608) by (clear - AG31 c30_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm8]).
  assert (c31_Sm16: L5.u64_at RSEGS M31 (S - 16) (U R0 8)) by (clear - AG31 c30_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm16]).
  assert (c31_Sm280w1: L5.u8_at RSEGS M31 (S - 280) fb280) by (clear - AG31 c30_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Sm280w1]).
  assert (c31_Sm248w1: L5.u8_at RSEGS M31 (S - 248) fb248) by (clear - AG31 c30_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Sm248w1]).
  assert (c31_Sm216w1: L5.u8_at RSEGS M31 (S - 216) fb216) by (clear - AG31 c30_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Sm216w1]).
  assert (c31_Sm192: L5.u64_at RSEGS M31 (S - 192) d3) by (clear - AG31 c30_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm192]).
  assert (c31_Sm200: L5.u64_at RSEGS M31 (S - 200) 8) by (clear - AG31 c30_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm200]).
  assert (c31_Sm184w1: L5.u8_at RSEGS M31 (S - 184) fb184) by (clear - AG31 c30_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Sm184w1]).
  assert (c31_Sm160: L5.u64_at RSEGS M31 (S - 160) d4) by (clear - AG31 c30_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm160]).
  assert (c31_Sm168: L5.u64_at RSEGS M31 (S - 168) 8) by (clear - AG31 c30_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Sm168]).
  assert (c31_Sm48w1: L5.u8_at RSEGS M31 (S - 48) fb48) by (clear - AG31 c30_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Sm48w1]).
  assert (c31_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M31 (A + i) 0)) by (clear - AG31 c30_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | apply c30_Om128z8; exact Hi]).
  assert (c31_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M31 ((A + 48) + i) 0)) by (clear - AG31 c30_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | apply c30_Om80z12; exact Hi]).
  assert (c31_Op0: L5.u64_at RSEGS M31 (A + 128) 373272) by (clear - AG31 c30_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Op0]).
  assert (c31_Op8: L5.u64_at RSEGS M31 (A + 136) (ref + 24)) by (clear - AG31 c30_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Op8]).
  assert (c31_Fp24: L5.u64_at RSEGS M31 (ref + 24) 8028075845441778529) by (clear - AG31 c30_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp24]).
  assert (c31_Fp32: L5.u64_at RSEGS M31 (ref + 32) 7863351059373564014) by (clear - AG31 c30_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp32]).
  assert (c31_Fp40: L5.u64_at RSEGS M31 (ref + 40) 2838809733452757089) by (clear - AG31 c30_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp40]).
  assert (c31_Fp48: L5.u64_at RSEGS M31 (ref + 48) 2334102023183623712) by (clear - AG31 c30_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp48]).
  assert (c31_Fp56: L5.u64_at RSEGS M31 (ref + 56) 4188416081412519009) by (clear - AG31 c30_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp56]).
  assert (c31_Fp64w1: L5.u8_at RSEGS M31 (ref + 64) 48) by (clear - AG31 c30_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Fp64w1]).
  assert (c31_Fp65w1: L5.u8_at RSEGS M31 (ref + 65) 0) by (clear - AG31 c30_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M30 M31 _ _ _ (AG31 _ 1)); [lia | exact c30_Fp65w1]).
  assert (c31_Fp16w4: L5.u32_at RSEGS M31 (ref + 16) 0) by (clear - AG31 c30_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M30 M31 _ _ _ (AG31 _ 4)); [lia | exact c30_Fp16w4]).
  assert (c31_Fp8: L5.u64_at RSEGS M31 (ref + 8) 41) by (clear - AG31 c30_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp8]).
  assert (c31_Fp0: L5.u64_at RSEGS M31 ref 41) by (clear - AG31 c30_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Fp0]).
  assert (c31_Om8: L5.u64_at RSEGS M31 (A + 120) S) by (clear - AG31 c30_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om8]).
  assert (c31_Om40: L5.u64_at RSEGS M31 (A + 88) (A + 128)) by (clear - AG31 c30_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om40]).
  assert (c31_Om48: L5.u64_at RSEGS M31 (A + 80) 133016) by (clear - AG31 c30_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om48]).
  assert (c31_Om56: L5.u64_at RSEGS M31 (A + 72) 91560) by (clear - AG31 c30_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om56]).
  assert (c31_Om64: L5.u64_at RSEGS M31 (A + 64) 91699) by (clear - AG31 c30_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om64]).
  assert (c31_Om68w4: L5.u32_at RSEGS M31 (A + 60) 1) by (clear - AG31 c30_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M30 M31 _ _ _ (AG31 _ 4)); [lia | exact c30_Om68w4]).
  assert (c31_Om16: L5.u64_at RSEGS M31 (A + 112) 0) by (clear - AG31 c30_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om16]).
  assert (c31_Om120: L5.u64_at RSEGS M31 (A + 8) 1) by (clear - AG31 c30_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om120]).
  assert (c31_Om24: L5.u64_at RSEGS M31 (A + 104) 257624) by (clear - AG31 c30_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om24]).
  assert (c31_Om32: L5.u64_at RSEGS M31 (A + 96) 4849336966747728640) by (clear - AG31 c30_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om32]).
  assert (c31_Om88: L5.u64_at RSEGS M31 (A + 40) 142700) by (clear - AG31 c30_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om88]).
  assert (c31_Om104: L5.u64_at RSEGS M31 (A + 24) 253816) by (clear - AG31 c30_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om104]).
  assert (c31_Om112: L5.u64_at RSEGS M31 (A + 16) 373232) by (clear - AG31 c30_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om112]).
  assert (c31_Om96: L5.u64_at RSEGS M31 (A + 32) 142968) by (clear - AG31 c30_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M30 M31 _ _ _ (AG31 _ 8)); [lia | exact c30_Om96]).
  assert (STAT31: forall a, stat_rd av a -> M31 (Z_to_bv 64 a) = M30 (Z_to_bv 64 a)).
  { clear - FR31 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR31; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M30 M31 gd av uid rnd canary hw ES30 STAT31) as ES31.
  assert (DEF31: L5.defined M31 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR31 | exact DEF30]).
  assert (DEFref_31: L5.defined M31 ref 66) by (eapply L5.defined_grows; [exact GR31 | exact DEFref_30]).
  assert (DEFA_31: L5.defined M31 A 144) by (eapply L5.defined_grows; [exact GR31 | exact DEFA_30]).
  assert (HH31: hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M31 (m_vmmaps model28)).
  { clear - HH30 GR31 FR31 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH30. lia. 2: exact GR31. intros a Ha.
    destruct (in_dec (S - 112) (S - 48) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR31; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ31: L5C.hpres L LB1 S 10240 XSF M M31).
  { clear - LBWF HQ30 FR31 GR31 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M30 M31 [((S - 112), 64)]). exact LBWF. lia. exact HQ30.
    { intros x Hx. apply FR31; intros Hin.
        apply (Hx ((S - 112), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR31.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG31 FR31 MS31. try clear STAT31. try clear K30.
  try clear c30_Sm56. try clear c30_Sm64. try clear c30_Sm72. try clear c30_Sm80. try clear c30_Sm88. try clear c30_Sm96. try clear c30_Sm104. try clear c30_Sm112. try clear c30_Sm120. try clear c30_Sm128. try clear c30_Sm136. try clear c30_Sm144. try clear c30_Sm152. try clear c30_Sm8. try clear c30_Sm16. try clear c30_Sm280w1. try clear c30_Sm248w1. try clear c30_Sm216w1. try clear c30_Sm192. try clear c30_Sm200. try clear c30_Sm184w1. try clear c30_Sm160. try clear c30_Sm168. try clear c30_Sm48w1. try clear c30_Om128z8. try clear c30_Om80z12. try clear c30_Op0. try clear c30_Op8. try clear c30_Fp24. try clear c30_Fp32. try clear c30_Fp40. try clear c30_Fp48. try clear c30_Fp56. try clear c30_Fp64w1. try clear c30_Fp65w1. try clear c30_Fp16w4. try clear c30_Fp8. try clear c30_Fp0. try clear c30_Om8. try clear c30_Om40. try clear c30_Om48. try clear c30_Om56. try clear c30_Om64. try clear c30_Om68w4. try clear c30_Om16. try clear c30_Om120. try clear c30_Om24. try clear c30_Om32. try clear c30_Om88. try clear c30_Om104. try clear c30_Om112. try clear c30_Om96. try clear R30_1. try clear R30_2. try clear R30_3. try clear R30_4. try clear R30_8. try clear R30_9. try clear R30_10. try clear R30_11. try clear R30_18. try clear R30_19. try clear R30_20. try clear R30_21. try clear R30_22. try clear R30_23. try clear R30_24. try clear R30_25. try clear R30_26. try clear R30_27. try clear DEF30. try clear HH30. try clear HQ30. try clear ES30. try clear DEFref_30. try clear DEFA_30.
  (* [comment removed for export] *)
  pose proof ES31 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M31 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3r6_conc fx31 R31 M31 (S - 896) (A + 128) av canary uid rnd hw (U R0 8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx32 & R32 & M32 & MS32 & K32 & R32_1 & R32_2 & R32_8 & R32_10 & R32_11 & FR32 & GR32).
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
  { (* [comment removed for export] *) unfold U; apply wrange. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF31 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF31); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF31 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF31); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_31 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_31); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_31 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_31); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c31_Om16 | cellfix c31_Om16]. }
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
  { (* [comment removed for export] *) first [exact c31_Om8 | cellfix c31_Om8]. }
  { (* [comment removed for export] *) first [exact c31_Om32 | cellfix c31_Om32]. }
  { (* [comment removed for export] *) first [exact c31_Sm8 | cellfix c31_Sm8]. }
  { (* [comment removed for export] *) first [exact c31_Sm16 | cellfix c31_Sm16]. }
  { (* [comment removed for export] *) first [exact c31_Om68w4 | cellfix c31_Om68w4]. }
  { (* [comment removed for export] *) first [exact c31_Om48 | cellfix c31_Om48]. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS32.
  (* [comment removed for export] *)
  assert (AG32: forall a k, ((a + k <= (S - 8832) \/ (S - 48) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M31 M32 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR32; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R32_1n: getr R32 (reg 1) = Z_to_bv 64 133016) by (rewrite R32_1; f_equal; ring). clear R32_1. rename R32_1n into R32_1.
  assert (R32_2n: getr R32 (reg 2) = Z_to_bv 64 S) by (rewrite R32_2; f_equal; ring). clear R32_2. rename R32_2n into R32_2.
  assert (R32_3: getr R32 (reg 3) = Z_to_bv 64 67584) by (kin K32 3%nat; exact R31_3).
  assert (R32_4: getr R32 (reg 4) = Z_to_bv 64 459832) by (kin K32 4%nat; exact R31_4).
  assert (R32_8n: getr R32 (reg 8) = Z_to_bv 64 (U R0 8)) by (rewrite R32_8; f_equal; ring). clear R32_8. rename R32_8n into R32_8.
  assert (R32_9: getr R32 (reg 9) = Z_to_bv 64 (U R0 9)) by (kin K32 9%nat; exact R31_9).
  assert (R32_10n: getr R32 (reg 10) = Z_to_bv 64 (A + 96)) by (rewrite R32_10; f_equal; ring). clear R32_10. rename R32_10n into R32_10.
  assert (R32_11n: getr R32 (reg 11) = Z_to_bv 64 1) by (rewrite R32_11; f_equal; ring). clear R32_11. rename R32_11n into R32_11.
  assert (R32_18: getr R32 (reg 18) = Z_to_bv 64 (U R0 18)) by (kin K32 18%nat; exact R31_18).
  assert (R32_19: getr R32 (reg 19) = Z_to_bv 64 (U R0 19)) by (kin K32 19%nat; exact R31_19).
  assert (R32_20: getr R32 (reg 20) = Z_to_bv 64 (U R0 20)) by (kin K32 20%nat; exact R31_20).
  assert (R32_21: getr R32 (reg 21) = Z_to_bv 64 (U R0 21)) by (kin K32 21%nat; exact R31_21).
  assert (R32_22: getr R32 (reg 22) = Z_to_bv 64 (U R0 22)) by (kin K32 22%nat; exact R31_22).
  assert (R32_23: getr R32 (reg 23) = Z_to_bv 64 (U R0 23)) by (kin K32 23%nat; exact R31_23).
  assert (R32_24: getr R32 (reg 24) = Z_to_bv 64 (U R0 24)) by (kin K32 24%nat; exact R31_24).
  assert (R32_25: getr R32 (reg 25) = Z_to_bv 64 (U R0 25)) by (kin K32 25%nat; exact R31_25).
  assert (R32_26: getr R32 (reg 26) = Z_to_bv 64 (U R0 26)) by (kin K32 26%nat; exact R31_26).
  assert (R32_27: getr R32 (reg 27) = Z_to_bv 64 (U R0 27)) by (kin K32 27%nat; exact R31_27).
  assert (c32_Sm8: L5.u64_at RSEGS M32 (S - 8) 132608) by (clear - AG32 c31_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Sm8]).
  assert (c32_Sm16: L5.u64_at RSEGS M32 (S - 16) (U R0 8)) by (clear - AG32 c31_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Sm16]).
  assert (c32_Sm48w1: L5.u8_at RSEGS M32 (S - 48) fb48) by (clear - AG32 c31_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M31 M32 _ _ _ (AG32 _ 1)); [lia | exact c31_Sm48w1]).
  assert (c32_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M32 (A + i) 0)) by (clear - AG32 c31_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M31 M32 _ _ _ (AG32 _ 1)); [lia | apply c31_Om128z8; exact Hi]).
  assert (c32_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M32 ((A + 48) + i) 0)) by (clear - AG32 c31_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M31 M32 _ _ _ (AG32 _ 1)); [lia | apply c31_Om80z12; exact Hi]).
  assert (c32_Op0: L5.u64_at RSEGS M32 (A + 128) 373272) by (clear - AG32 c31_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Op0]).
  assert (c32_Op8: L5.u64_at RSEGS M32 (A + 136) (ref + 24)) by (clear - AG32 c31_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Op8]).
  assert (c32_Fp24: L5.u64_at RSEGS M32 (ref + 24) 8028075845441778529) by (clear - AG32 c31_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp24]).
  assert (c32_Fp32: L5.u64_at RSEGS M32 (ref + 32) 7863351059373564014) by (clear - AG32 c31_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp32]).
  assert (c32_Fp40: L5.u64_at RSEGS M32 (ref + 40) 2838809733452757089) by (clear - AG32 c31_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp40]).
  assert (c32_Fp48: L5.u64_at RSEGS M32 (ref + 48) 2334102023183623712) by (clear - AG32 c31_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp48]).
  assert (c32_Fp56: L5.u64_at RSEGS M32 (ref + 56) 4188416081412519009) by (clear - AG32 c31_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp56]).
  assert (c32_Fp64w1: L5.u8_at RSEGS M32 (ref + 64) 48) by (clear - AG32 c31_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M31 M32 _ _ _ (AG32 _ 1)); [lia | exact c31_Fp64w1]).
  assert (c32_Fp65w1: L5.u8_at RSEGS M32 (ref + 65) 0) by (clear - AG32 c31_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M31 M32 _ _ _ (AG32 _ 1)); [lia | exact c31_Fp65w1]).
  assert (c32_Fp16w4: L5.u32_at RSEGS M32 (ref + 16) 0) by (clear - AG32 c31_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M31 M32 _ _ _ (AG32 _ 4)); [lia | exact c31_Fp16w4]).
  assert (c32_Fp8: L5.u64_at RSEGS M32 (ref + 8) 41) by (clear - AG32 c31_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp8]).
  assert (c32_Fp0: L5.u64_at RSEGS M32 ref 41) by (clear - AG32 c31_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Fp0]).
  assert (c32_Om8: L5.u64_at RSEGS M32 (A + 120) S) by (clear - AG32 c31_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om8]).
  assert (c32_Om40: L5.u64_at RSEGS M32 (A + 88) (A + 128)) by (clear - AG32 c31_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om40]).
  assert (c32_Om48: L5.u64_at RSEGS M32 (A + 80) 133016) by (clear - AG32 c31_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om48]).
  assert (c32_Om56: L5.u64_at RSEGS M32 (A + 72) 91560) by (clear - AG32 c31_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om56]).
  assert (c32_Om64: L5.u64_at RSEGS M32 (A + 64) 91699) by (clear - AG32 c31_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om64]).
  assert (c32_Om68w4: L5.u32_at RSEGS M32 (A + 60) 1) by (clear - AG32 c31_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M31 M32 _ _ _ (AG32 _ 4)); [lia | exact c31_Om68w4]).
  assert (c32_Om16: L5.u64_at RSEGS M32 (A + 112) 0) by (clear - AG32 c31_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om16]).
  assert (c32_Om120: L5.u64_at RSEGS M32 (A + 8) 1) by (clear - AG32 c31_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om120]).
  assert (c32_Om24: L5.u64_at RSEGS M32 (A + 104) 257624) by (clear - AG32 c31_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om24]).
  assert (c32_Om32: L5.u64_at RSEGS M32 (A + 96) 4849336966747728640) by (clear - AG32 c31_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om32]).
  assert (c32_Om88: L5.u64_at RSEGS M32 (A + 40) 142700) by (clear - AG32 c31_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om88]).
  assert (c32_Om104: L5.u64_at RSEGS M32 (A + 24) 253816) by (clear - AG32 c31_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om104]).
  assert (c32_Om112: L5.u64_at RSEGS M32 (A + 16) 373232) by (clear - AG32 c31_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om112]).
  assert (c32_Om96: L5.u64_at RSEGS M32 (A + 32) 142968) by (clear - AG32 c31_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M31 M32 _ _ _ (AG32 _ 8)); [lia | exact c31_Om96]).
  assert (STAT32: forall a, stat_rd av a -> M32 (Z_to_bv 64 a) = M31 (Z_to_bv 64 a)).
  { clear - FR32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR32; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M31 M32 gd av uid rnd canary hw ES31 STAT32) as ES32.
  assert (DEF32: L5.defined M32 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR32 | exact DEF31]).
  assert (DEFref_32: L5.defined M32 ref 66) by (eapply L5.defined_grows; [exact GR32 | exact DEFref_31]).
  assert (DEFA_32: L5.defined M32 A 144) by (eapply L5.defined_grows; [exact GR32 | exact DEFA_31]).
  assert (HH32: hi_heap HI ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M32 (m_vmmaps model28)).
  { clear - HH31 GR32 FR32 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH31. lia. 2: exact GR32. intros a Ha.
    destruct (in_dec (S - 8832) (S - 48) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR32; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ32: L5C.hpres L LB1 S 10240 XSF M M32).
  { clear - LBWF HQ31 FR32 GR32 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M31 M32 [((S - 8832), 8784)]). exact LBWF. lia. exact HQ31.
    { intros x Hx. apply FR32; intros Hin.
        apply (Hx ((S - 8832), 8784)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR32.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG32 FR32 MS32. try clear STAT32. try clear K31.
  try clear c31_Sm120. try clear c31_Sm128. try clear c31_Sm136. try clear c31_Sm144. try clear c31_Sm152. try clear c31_Sm8. try clear c31_Sm16. try clear c31_Sm280w1. try clear c31_Sm248w1. try clear c31_Sm216w1. try clear c31_Sm192. try clear c31_Sm200. try clear c31_Sm184w1. try clear c31_Sm160. try clear c31_Sm168. try clear c31_Sm48w1. try clear c31_Om128z8. try clear c31_Om80z12. try clear c31_Op0. try clear c31_Op8. try clear c31_Fp24. try clear c31_Fp32. try clear c31_Fp40. try clear c31_Fp48. try clear c31_Fp56. try clear c31_Fp64w1. try clear c31_Fp65w1. try clear c31_Fp16w4. try clear c31_Fp8. try clear c31_Fp0. try clear c31_Om8. try clear c31_Om40. try clear c31_Om48. try clear c31_Om56. try clear c31_Om64. try clear c31_Om68w4. try clear c31_Om16. try clear c31_Om120. try clear c31_Om24. try clear c31_Om32. try clear c31_Om88. try clear c31_Om104. try clear c31_Om112. try clear c31_Om96. try clear R31_1. try clear R31_2. try clear R31_3. try clear R31_4. try clear R31_8. try clear R31_9. try clear R31_10. try clear R31_11. try clear R31_18. try clear R31_19. try clear R31_20. try clear R31_21. try clear R31_22. try clear R31_23. try clear R31_24. try clear R31_25. try clear R31_26. try clear R31_27. try clear DEF31. try clear HH31. try clear HQ31. try clear ES31. try clear DEFref_31. try clear DEFA_31.
  (* [comment removed for export] *)
  specialize (KE fx32 R32 M32 model28 ((ref, 66) :: (A, 144) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66)). apply KE; clear KE.
  - apply L5CoreKit.L5K.regs_preserved_by_index. intros i Hi. cbn in Hi.
    destruct Hi as [<-|Hi]. { rewrite R32_2, H02. f_equal; alia0. }
    destruct Hi as [<-|Hi]. { rewrite R32_3, H03. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite R32_4, H04. reflexivity. }
    destruct Hi as [<-|Hi]. { rewrite R32_8. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_9. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_18. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_19. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_20. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_21. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_22. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_23. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_24. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_25. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_26. unfold U. apply lit_of_word. }
    destruct Hi as [<-|Hi]. { rewrite R32_27. unfold U. apply lit_of_word. }
    destruct Hi.
  - unfold L5US.e3_landed, L5US.REF3_SZ, L5US.EXC23_SZ. exists (A + 128), ref. cbn [L5US.xs_gd L5US.xs_av L5US.xs_uid L5US.xs_rnd L5US.xs_canary L5US.xs_hw L5US.xs_of].
    replace (A + 128 - 128) with A by alia0.
    split. { rewrite L5CoreKit.L5K.rl10, R32_10. f_equal; alia0. }
    split. { rewrite L5CoreKit.L5K.rl11, R32_11. f_equal; alia0. }
    split. { rewrite L5CoreKit.L5K.rl2, R32_2. f_equal; alia0. }
    split. reflexivity.
    split. { split. exact BR_A. split. destruct FRSH_A as (_ & _ & _ & BAA); exact BAA. exact DEFA_32. }
    split. { split. exact BR_ref. split. { destruct FRSH_ref as (_ & _ & _ & BAr). intros b [<-|Hb]. cbn [fst snd]. alia1. apply BAr. exact Hb. } exact DEFref_32. }
    split. { unfold L5US.exc_blocks_ok. replace (A + 128 - 128) with A by alia0. assert (HA1: L5.hull_apart RSEGS A 144) by (apply hull_apart_of; exact B1_A).
             assert (HA2: L5.hull_apart RSEGS ref 66) by (apply hull_apart_of; exact B1_ref). repeat split; first [assumption | alia1]. }
    split. { unfold L5US.exc3_at, L5US.exc_hdr, L5US.TI_ASSERTION_ERROR, L5US.DTOR_RUNTIME_ERROR, L5US.UNEXPECTED_H, L5US.TERMINATE_H, L5US.EXC_ACTION, L5US.EXC_LSDA,
             L5US.TOP_PAD, L5US.EXC_CLASS, L5US.UE_CLEANUP, L5US.VT_ASSERTION_ERROR.
      split.
      - split. intros i Hi; lazymatch goal with |- L5.u8_at _ _ ?a0 _ => replace a0 with (A + i) by ring end; apply c32_Om128z8; exact Hi.
        split. cellfix c32_Om120.
        split. cellfix c32_Om112.
        split. cellfix c32_Om104.
        split. cellfix c32_Om96.
        split. cellfix c32_Om88.
        split. intros i Hi; lazymatch goal with |- L5.u8_at _ _ ?a0 _ => replace a0 with ((A + 48) + i) by ring end; apply c32_Om80z12; exact Hi.
        split. cellfix c32_Om68w4.
        split. cellfix c32_Om64.
        split. cellfix c32_Om56.
        split. cellfix c32_Om48.
        split. cellfix c32_Om40.
        split. cellfix c32_Om32.
        split. cellfix c32_Om24.
        split. cellfix c32_Om16.
        cellfix c32_Om8.
      - split. cellfix c32_Op0. split. cellfix c32_Op8.
        apply (refstring3_of_cells M32 ref); [alia0 | alia0 | cellfix c32_Fp0 | cellfix c32_Fp8 | cellfix c32_Fp16w4 | cellfix c32_Fp24 | cellfix c32_Fp32 | cellfix c32_Fp40 | cellfix c32_Fp48 | cellfix c32_Fp56 | cellfix c32_Fp64w1 | cellfix c32_Fp65w1]. }
    split. exact ES32.
    unfold credit_le, debit. cbn. alia0.
  - exact HQ32.
  - exact MBV28.
  - exact HH32.
Qed.
End WithHeap.
End SCFG_2.
End L5E3S17.
