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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S15.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S14.
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
Let seg15 := L5E3S15.seg15 L HI LY LYX HIok.

Lemma seg14 (fx24 : FPState) (R0 R R24 : bvmap 5 word) (M M24 : word -> option byte) (model model18 : Model) (K : TSet)
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
  (* [comment removed for export] *) getr R24 (reg 1) = Z_to_bv 64 140244 ->
  (* [comment removed for export] *) getr R24 (reg 2) = Z_to_bv 64 (S - 352) ->
  (* [comment removed for export] *) getr R24 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R24 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R24 (reg 8) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R24 (reg 9) = Z_to_bv 64 (S - 48) ->
  (* [comment removed for export] *) getr R24 (reg 10) = Z_to_bv 64 (A + 96) ->
  (* [comment removed for export] *) getr R24 (reg 11) = Z_to_bv 64 0 ->
  (* [comment removed for export] *) getr R24 (reg 18) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R24 (reg 19) = Z_to_bv 64 w504 ->
  (* [comment removed for export] *) getr R24 (reg 20) = Z_to_bv 64 w512 ->
  (* [comment removed for export] *) getr R24 (reg 21) = Z_to_bv 64 w520 ->
  (* [comment removed for export] *) getr R24 (reg 22) = Z_to_bv 64 w528 ->
  (* [comment removed for export] *) getr R24 (reg 23) = Z_to_bv 64 w536 ->
  (* [comment removed for export] *) getr R24 (reg 24) = Z_to_bv 64 w544 ->
  (* [comment removed for export] *) getr R24 (reg 25) = Z_to_bv 64 w552 ->
  (* [comment removed for export] *) getr R24 (reg 26) = Z_to_bv 64 w560 ->
  (* [comment removed for export] *) getr R24 (reg 27) = Z_to_bv 64 w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (S - 48) fb48 ->
  (* [comment removed for export] *) (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M24 (A + i) 0) ->
  (* [comment removed for export] *) (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M24 ((A + 48) + i) 0) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 128) 373272 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 136) (ref + 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 24) 8028075845441778529 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 32) 7863351059373564014 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 40) 2838809733452757089 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 48) 2334102023183623712 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 56) 4188416081412519009 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (ref + 64) 48 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M24 (ref + 65) 0 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M24 (ref + 16) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (ref + 8) 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 ref 41 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 120) S ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 88) (A + 128) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 80) 133016 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 72) 91560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 64) 91699 ->
  (* [comment removed for export] *) L5.u32_at RSEGS M24 (A + 60) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 112) 0 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 8) 1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 104) 257624 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 96) 4849336966747728640 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 40) 142700 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 24) 253816 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 16) 373232 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M24 (A + 32) 142968 ->
  (* [comment removed for export] *) L5US.statics_landed M24 gd av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M24 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M24 ref 66 ->
  (* [comment removed for export] *) L5.defined M24 A 144 ->
  (* [comment removed for export] *) L5.defined M24 d3 64 ->
  (* [comment removed for export] *) L5.defined M24 d4 64 ->
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
  (* [comment removed for export] *) hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M24 (m_vmmaps model18) ->
  (* [comment removed for export] *) model_ok model18 ->
  (* [comment removed for export] *) model_but_vm model model18 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M24 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx24 R24 140244 M24 model18) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R24_1 R24_2 R24_3 R24_4 R24_8 R24_9 R24_10 R24_11 R24_18 R24_19 R24_20 R24_21 R24_22 R24_23 R24_24 R24_25 R24_26 R24_27 c24_Sm360 c24_Sm368 c24_Sm376 c24_Sm56 c24_Sm64 c24_Sm72 c24_Sm80 c24_Sm88 c24_Sm96 c24_Sm104 c24_Sm112 c24_Sm120 c24_Sm128 c24_Sm136 c24_Sm144 c24_Sm152 c24_Sm8 c24_Sm16 c24_Sm408w1 c24_Sm280w1 c24_Sm248w1 c24_Sm216w1 c24_Sm192 c24_Sm200 c24_Sm184w1 c24_Sm160 c24_Sm168 c24_Sm48w1 c24_Om128z8 c24_Om80z12 c24_Op0 c24_Op8 c24_Fp24 c24_Fp32 c24_Fp40 c24_Fp48 c24_Fp56 c24_Fp64w1 c24_Fp65w1 c24_Fp16w4 c24_Fp8 c24_Fp0 c24_Om8 c24_Om40 c24_Om48 c24_Om56 c24_Om64 c24_Om68w4 c24_Om16 c24_Om120 c24_Om24 c24_Om32 c24_Om88 c24_Om104 c24_Om112 c24_Om96 ES24 DEF24 DEFref_24 DEFA_24 DEFd3_24 DEFd4_24 BR_ref BR_A BR_d3 BR_d4 AP_ref_A AP_ref_d3 AP_ref_d4 AP_A_d3 AP_A_d4 AP_d3_d4 FRSH_ref FRSH_A HH24 MOK18 MBV18 HQ24 KE.
  pose proof MOK18 as (Mh & Ml & Mm).
  pose proof BR_ref as (B0_ref & B1_ref & B2_ref & B3_ref & B4_ref). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_ref. unfold hl_ceil in B4_ref.
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES24 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20 & S_21 & S_22 & S_23 & S_24 & S_25).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9, S_10, S_11, S_12, S_13, S_14.
  pose proof (auxv_cells M24 av uid rnd hw S_18) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  unshelve epose proof (e3p5_conc fx24 R24 M24 (S - 896) (A + 128) fb280 fb248 fb216 d3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx25 & R25 & M25 & MS25 & K25 & R25_1 & R25_2 & R25_8 & R25_10 & R25_11 & FR25 & GR25).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb280. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb248. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb216. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF24); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF24); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_24); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_24); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d3 B1_d3 B3_d3 B4_d3 AP_A_d3. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb280. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb248. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Hr_fb216. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c24_Sm280w1 | cellfix c24_Sm280w1]. }
  { (* [comment removed for export] *) rewrite land254_bit0 by (assumption || kl). first [exact c24_Sm248w1 | cellfix c24_Sm248w1]. }
  { (* [comment removed for export] *) rewrite lor1_land254_bit1 by (assumption || kl). first [exact c24_Sm216w1 | cellfix c24_Sm216w1]. }
  { (* [comment removed for export] *) first [exact c24_Sm192 | cellfix c24_Sm192]. }
  { (* [comment removed for export] *) first [exact c24_Sm200 | cellfix c24_Sm200]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS25.
  (* [comment removed for export] *)
  assert (AG25: forall a k, ((a + k <= (S - 416) \/ (S - 352) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M24 M25 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR25; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R25_1n: getr R25 (reg 1) = Z_to_bv 64 140348) by (rewrite R25_1; f_equal; ring). clear R25_1. rename R25_1n into R25_1.
  assert (R25_2n: getr R25 (reg 2) = Z_to_bv 64 (S - 352)) by (rewrite R25_2; f_equal; ring). clear R25_2. rename R25_2n into R25_2.
  assert (R25_3: getr R25 (reg 3) = Z_to_bv 64 67584) by (kin K25 3%nat; exact R24_3).
  assert (R25_4: getr R25 (reg 4) = Z_to_bv 64 459832) by (kin K25 4%nat; exact R24_4).
  assert (R25_8n: getr R25 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite R25_8; f_equal; ring). clear R25_8. rename R25_8n into R25_8.
  assert (R25_9: getr R25 (reg 9) = Z_to_bv 64 (S - 48)) by (kin K25 9%nat; exact R24_9).
  assert (R25_10n: getr R25 (reg 10) = Z_to_bv 64 d3) by (rewrite R25_10; f_equal; ring). clear R25_10. rename R25_10n into R25_10.
  assert (R25_11n: getr R25 (reg 11) = Z_to_bv 64 64) by (rewrite R25_11; f_equal; ring). clear R25_11. rename R25_11n into R25_11.
  assert (R25_18: getr R25 (reg 18) = Z_to_bv 64 (S + 64)) by (kin K25 18%nat; exact R24_18).
  assert (R25_19: getr R25 (reg 19) = Z_to_bv 64 w504) by (kin K25 19%nat; exact R24_19).
  assert (R25_20: getr R25 (reg 20) = Z_to_bv 64 w512) by (kin K25 20%nat; exact R24_20).
  assert (R25_21: getr R25 (reg 21) = Z_to_bv 64 w520) by (kin K25 21%nat; exact R24_21).
  assert (R25_22: getr R25 (reg 22) = Z_to_bv 64 w528) by (kin K25 22%nat; exact R24_22).
  assert (R25_23: getr R25 (reg 23) = Z_to_bv 64 w536) by (kin K25 23%nat; exact R24_23).
  assert (R25_24: getr R25 (reg 24) = Z_to_bv 64 w544) by (kin K25 24%nat; exact R24_24).
  assert (R25_25: getr R25 (reg 25) = Z_to_bv 64 w552) by (kin K25 25%nat; exact R24_25).
  assert (R25_26: getr R25 (reg 26) = Z_to_bv 64 w560) by (kin K25 26%nat; exact R24_26).
  assert (R25_27: getr R25 (reg 27) = Z_to_bv 64 w568) by (kin K25 27%nat; exact R24_27).
  assert (c25_Sm56: L5.u64_at RSEGS M25 (S - 56) 138528) by (clear - AG25 c24_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm56]).
  assert (c25_Sm64: L5.u64_at RSEGS M25 (S - 64) (S + 64)) by (clear - AG25 c24_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm64]).
  assert (c25_Sm72: L5.u64_at RSEGS M25 (S - 72) (U R0 9)) by (clear - AG25 c24_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm72]).
  assert (c25_Sm80: L5.u64_at RSEGS M25 (S - 80) (U R0 18)) by (clear - AG25 c24_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm80]).
  assert (c25_Sm88: L5.u64_at RSEGS M25 (S - 88) (U R0 19)) by (clear - AG25 c24_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm88]).
  assert (c25_Sm96: L5.u64_at RSEGS M25 (S - 96) (U R0 20)) by (clear - AG25 c24_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm96]).
  assert (c25_Sm104: L5.u64_at RSEGS M25 (S - 104) (U R0 21)) by (clear - AG25 c24_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm104]).
  assert (c25_Sm112: L5.u64_at RSEGS M25 (S - 112) (U R0 22)) by (clear - AG25 c24_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm112]).
  assert (c25_Sm120: L5.u64_at RSEGS M25 (S - 120) (U R0 23)) by (clear - AG25 c24_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm120]).
  assert (c25_Sm128: L5.u64_at RSEGS M25 (S - 128) (U R0 24)) by (clear - AG25 c24_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm128]).
  assert (c25_Sm136: L5.u64_at RSEGS M25 (S - 136) (U R0 25)) by (clear - AG25 c24_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm136]).
  assert (c25_Sm144: L5.u64_at RSEGS M25 (S - 144) (U R0 26)) by (clear - AG25 c24_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm144]).
  assert (c25_Sm152: L5.u64_at RSEGS M25 (S - 152) (U R0 27)) by (clear - AG25 c24_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm152]).
  assert (c25_Sm8: L5.u64_at RSEGS M25 (S - 8) 132608) by (clear - AG25 c24_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm8]).
  assert (c25_Sm16: L5.u64_at RSEGS M25 (S - 16) (U R0 8)) by (clear - AG25 c24_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm16]).
  assert (c25_Sm280w1: L5.u8_at RSEGS M25 (S - 280) fb280) by (clear - AG25 c24_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Sm280w1]).
  assert (c25_Sm248w1: L5.u8_at RSEGS M25 (S - 248) fb248) by (clear - AG25 c24_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Sm248w1]).
  assert (c25_Sm216w1: L5.u8_at RSEGS M25 (S - 216) fb216) by (clear - AG25 c24_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Sm216w1]).
  assert (c25_Sm192: L5.u64_at RSEGS M25 (S - 192) d3) by (clear - AG25 c24_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm192]).
  assert (c25_Sm200: L5.u64_at RSEGS M25 (S - 200) 8) by (clear - AG25 c24_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm200]).
  assert (c25_Sm184w1: L5.u8_at RSEGS M25 (S - 184) fb184) by (clear - AG25 c24_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Sm184w1]).
  assert (c25_Sm160: L5.u64_at RSEGS M25 (S - 160) d4) by (clear - AG25 c24_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm160]).
  assert (c25_Sm168: L5.u64_at RSEGS M25 (S - 168) 8) by (clear - AG25 c24_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Sm168]).
  assert (c25_Sm48w1: L5.u8_at RSEGS M25 (S - 48) fb48) by (clear - AG25 c24_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Sm48w1]).
  assert (c25_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M25 (A + i) 0)) by (clear - AG25 c24_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | apply c24_Om128z8; exact Hi]).
  assert (c25_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M25 ((A + 48) + i) 0)) by (clear - AG25 c24_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | apply c24_Om80z12; exact Hi]).
  assert (c25_Op0: L5.u64_at RSEGS M25 (A + 128) 373272) by (clear - AG25 c24_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Op0]).
  assert (c25_Op8: L5.u64_at RSEGS M25 (A + 136) (ref + 24)) by (clear - AG25 c24_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Op8]).
  assert (c25_Fp24: L5.u64_at RSEGS M25 (ref + 24) 8028075845441778529) by (clear - AG25 c24_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp24]).
  assert (c25_Fp32: L5.u64_at RSEGS M25 (ref + 32) 7863351059373564014) by (clear - AG25 c24_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp32]).
  assert (c25_Fp40: L5.u64_at RSEGS M25 (ref + 40) 2838809733452757089) by (clear - AG25 c24_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp40]).
  assert (c25_Fp48: L5.u64_at RSEGS M25 (ref + 48) 2334102023183623712) by (clear - AG25 c24_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp48]).
  assert (c25_Fp56: L5.u64_at RSEGS M25 (ref + 56) 4188416081412519009) by (clear - AG25 c24_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp56]).
  assert (c25_Fp64w1: L5.u8_at RSEGS M25 (ref + 64) 48) by (clear - AG25 c24_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Fp64w1]).
  assert (c25_Fp65w1: L5.u8_at RSEGS M25 (ref + 65) 0) by (clear - AG25 c24_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr8 M24 M25 _ _ _ (AG25 _ 1)); [lia | exact c24_Fp65w1]).
  assert (c25_Fp16w4: L5.u32_at RSEGS M25 (ref + 16) 0) by (clear - AG25 c24_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr32 M24 M25 _ _ _ (AG25 _ 4)); [lia | exact c24_Fp16w4]).
  assert (c25_Fp8: L5.u64_at RSEGS M25 (ref + 8) 41) by (clear - AG25 c24_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp8]).
  assert (c25_Fp0: L5.u64_at RSEGS M25 ref 41) by (clear - AG25 c24_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Fp0]).
  assert (c25_Om8: L5.u64_at RSEGS M25 (A + 120) S) by (clear - AG25 c24_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om8]).
  assert (c25_Om40: L5.u64_at RSEGS M25 (A + 88) (A + 128)) by (clear - AG25 c24_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om40]).
  assert (c25_Om48: L5.u64_at RSEGS M25 (A + 80) 133016) by (clear - AG25 c24_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om48]).
  assert (c25_Om56: L5.u64_at RSEGS M25 (A + 72) 91560) by (clear - AG25 c24_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om56]).
  assert (c25_Om64: L5.u64_at RSEGS M25 (A + 64) 91699) by (clear - AG25 c24_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om64]).
  assert (c25_Om68w4: L5.u32_at RSEGS M25 (A + 60) 1) by (clear - AG25 c24_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr32 M24 M25 _ _ _ (AG25 _ 4)); [lia | exact c24_Om68w4]).
  assert (c25_Om16: L5.u64_at RSEGS M25 (A + 112) 0) by (clear - AG25 c24_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om16]).
  assert (c25_Om120: L5.u64_at RSEGS M25 (A + 8) 1) by (clear - AG25 c24_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om120]).
  assert (c25_Om24: L5.u64_at RSEGS M25 (A + 104) 257624) by (clear - AG25 c24_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om24]).
  assert (c25_Om32: L5.u64_at RSEGS M25 (A + 96) 4849336966747728640) by (clear - AG25 c24_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om32]).
  assert (c25_Om88: L5.u64_at RSEGS M25 (A + 40) 142700) by (clear - AG25 c24_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om88]).
  assert (c25_Om104: L5.u64_at RSEGS M25 (A + 24) 253816) by (clear - AG25 c24_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om104]).
  assert (c25_Om112: L5.u64_at RSEGS M25 (A + 16) 373232) by (clear - AG25 c24_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om112]).
  assert (c25_Om96: L5.u64_at RSEGS M25 (A + 32) 142968) by (clear - AG25 c24_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M24 M25 _ _ _ (AG25 _ 8)); [lia | exact c24_Om96]).
  assert (STAT25: forall a, stat_rd av a -> M25 (Z_to_bv 64 a) = M24 (Z_to_bv 64 a)).
  { clear - FR25 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR25; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (statics_landed_keep M24 M25 gd av uid rnd canary hw ES24 STAT25) as ES25.
  assert (DEF25: L5.defined M25 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR25 | exact DEF24]).
  assert (DEFref_25: L5.defined M25 ref 66) by (eapply L5.defined_grows; [exact GR25 | exact DEFref_24]).
  assert (DEFA_25: L5.defined M25 A 144) by (eapply L5.defined_grows; [exact GR25 | exact DEFA_24]).
  assert (DEFd3_25: L5.defined M25 d3 64) by (eapply L5.defined_grows; [exact GR25 | exact DEFd3_24]).
  assert (DEFd4_25: L5.defined M25 d4 64) by (eapply L5.defined_grows; [exact GR25 | exact DEFd4_24]).
  assert (HH25: hi_heap HI ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) M25 (m_vmmaps model18)).
  { clear - HH24 GR25 FR25 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH24. lia. 2: exact GR25. intros a Ha.
    destruct (in_dec (S - 416) (S - 352) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR25; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ25: L5C.hpres L LB1 S 10240 XSF M M25).
  { clear - LBWF HQ24 FR25 GR25 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M24 M25 [((S - 416), 64)]). exact LBWF. lia. exact HQ24.
    { intros x Hx. apply FR25; intros Hin.
        apply (Hx ((S - 416), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR25.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20 S_21 S_22 S_23 S_24 S_25. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG25 FR25 MS25. try clear STAT25. try clear K24.
  try clear c24_Sm360. try clear c24_Sm368. try clear c24_Sm376. try clear c24_Sm56. try clear c24_Sm64. try clear c24_Sm72. try clear c24_Sm80. try clear c24_Sm88. try clear c24_Sm96. try clear c24_Sm104. try clear c24_Sm112. try clear c24_Sm120. try clear c24_Sm128. try clear c24_Sm136. try clear c24_Sm144. try clear c24_Sm152. try clear c24_Sm8. try clear c24_Sm16. try clear c24_Sm408w1. try clear c24_Sm280w1. try clear c24_Sm248w1. try clear c24_Sm216w1. try clear c24_Sm192. try clear c24_Sm200. try clear c24_Sm184w1. try clear c24_Sm160. try clear c24_Sm168. try clear c24_Sm48w1. try clear c24_Om128z8. try clear c24_Om80z12. try clear c24_Op0. try clear c24_Op8. try clear c24_Fp24. try clear c24_Fp32. try clear c24_Fp40. try clear c24_Fp48. try clear c24_Fp56. try clear c24_Fp64w1. try clear c24_Fp65w1. try clear c24_Fp16w4. try clear c24_Fp8. try clear c24_Fp0. try clear c24_Om8. try clear c24_Om40. try clear c24_Om48. try clear c24_Om56. try clear c24_Om64. try clear c24_Om68w4. try clear c24_Om16. try clear c24_Om120. try clear c24_Om24. try clear c24_Om32. try clear c24_Om88. try clear c24_Om104. try clear c24_Om112. try clear c24_Om96. try clear R24_1. try clear R24_2. try clear R24_3. try clear R24_4. try clear R24_8. try clear R24_9. try clear R24_10. try clear R24_11. try clear R24_18. try clear R24_19. try clear R24_20. try clear R24_21. try clear R24_22. try clear R24_23. try clear R24_24. try clear R24_25. try clear R24_26. try clear R24_27. try clear DEF24. try clear HH24. try clear HQ24. try clear ES24. try clear DEFref_24. try clear DEFA_24. try clear DEFd3_24. try clear DEFd4_24.
  (* [comment removed for export] *)
  pose proof (hio_free L SCFG HI HIok fx25 R25 M25 model18 ((ref, 66) :: (A, 144) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (debit L (debit L (cr) 144) 48) 66) d3 64 K) as HC.
  rewrite (ly_segs L LY), (ly_free L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH25.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - right; right; left; reflexivity.
  - rewrite L5CoreKit.L5K.rl10. exact R25_10.
  - rewrite L5CoreKit.L5K.rl4. exact R25_4.
  - rewrite L5CoreKit.L5K.rl1, R25_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R25_2 A16 DEF25 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R25_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-22) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M25 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF25. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R26 M26 model26 RP26 [PRES26 _] MBVn HH26.
    rewrite L5CoreKit.L5K.rl1, R25_1.
    cbn [lb_remove fst app] in PRES26, HH26.
    rewrite (proj2 (Z.eqb_neq ref d3) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref B0_d3 B1_d3 B3_d3 B4_d3 AP_ref_d3)) in PRES26, HH26.
    rewrite (proj2 (Z.eqb_neq A d3) ltac:(kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A B0_d3 B1_d3 B3_d3 B4_d3 AP_A_d3)) in PRES26, HH26.
    rewrite Z.eqb_refl in PRES26, HH26.
    rewrite L5CoreKit.L5K.rl2, R25_2, BG.unsigned_lit in PRES26 by (kl SLO SHI STOP).
    match type of PRES26 with heap_pres_core _ _ ?x _ _ => replace x with (S - 352) in PRES26 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (S - 352) M25 M26 PRES26) as HP26. rewrite (ly_stack L LY) in HP26. unfold HEAP_STACK in HP26.
    assert (AGS26: forall a k, ((S - 352) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M25 M26 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP26 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP26. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB26_ref: L5C.agree_on M25 M26 ref 66).
    { clear - HP26 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP26. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_ref. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB26_A: L5C.agree_on M25 M26 A 144).
    { clear - HP26 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP26. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB26_d4: L5C.agree_on M25 M26 d4 64).
    { clear - HP26 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP26. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT26: forall a, stat_rd av a -> M26 (Z_to_bv 64 a) = M25 (Z_to_bv 64 a)).
    { clear - HP26 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (S - 352) 8224 [] M25 M26 HP26). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (statics_landed_keep M25 M26 gd av uid rnd canary hw ES25 STAT26) as ES26.
    assert (DEF26: L5.defined M26 (S - 10240) 10240).
    { clear - HP26 DEF25 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) (S - 352) 8224 [] M25 M26). exact HP26. lia. lia. lia. lia. exact DEF25. }
    assert (DEFref_26: L5.defined M26 ref 66) by (eapply (L5C.defined_agree M25 M26); [exact AGB26_ref | exact DEFref_25]).
    assert (DEFA_26: L5.defined M26 A 144) by (eapply (L5C.defined_agree M25 M26); [exact AGB26_A | exact DEFA_25]).
    assert (DEFd4_26: L5.defined M26 d4 64) by (eapply (L5C.defined_agree M25 M26); [exact AGB26_d4 | exact DEFd4_25]).
    assert (MOK26: model_ok model26).
    { destruct MOK18 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK26 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV18 MBVn) as MBV26. clear MBVn MBV18.
    assert (RPi26: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R26 (reg i) = getr R25 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R25 R26 i RP26). exact Hi. }
    assert (R26_2: getr R26 (reg 2) = Z_to_bv 64 (S - 352)) by (rewrite (RPi26 2%nat) by inl; exact R25_2).
    assert (R26_3: getr R26 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi26 3%nat) by inl; exact R25_3).
    assert (R26_4: getr R26 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi26 4%nat) by inl; exact R25_4).
    assert (R26_8: getr R26 (reg 8) = Z_to_bv 64 (A + 96)) by (rewrite (RPi26 8%nat) by inl; exact R25_8).
    assert (R26_9: getr R26 (reg 9) = Z_to_bv 64 (S - 48)) by (rewrite (RPi26 9%nat) by inl; exact R25_9).
    assert (R26_18: getr R26 (reg 18) = Z_to_bv 64 (S + 64)) by (rewrite (RPi26 18%nat) by inl; exact R25_18).
    assert (R26_19: getr R26 (reg 19) = Z_to_bv 64 w504) by (rewrite (RPi26 19%nat) by inl; exact R25_19).
    assert (R26_20: getr R26 (reg 20) = Z_to_bv 64 w512) by (rewrite (RPi26 20%nat) by inl; exact R25_20).
    assert (R26_21: getr R26 (reg 21) = Z_to_bv 64 w520) by (rewrite (RPi26 21%nat) by inl; exact R25_21).
    assert (R26_22: getr R26 (reg 22) = Z_to_bv 64 w528) by (rewrite (RPi26 22%nat) by inl; exact R25_22).
    assert (R26_23: getr R26 (reg 23) = Z_to_bv 64 w536) by (rewrite (RPi26 23%nat) by inl; exact R25_23).
    assert (R26_24: getr R26 (reg 24) = Z_to_bv 64 w544) by (rewrite (RPi26 24%nat) by inl; exact R25_24).
    assert (R26_25: getr R26 (reg 25) = Z_to_bv 64 w552) by (rewrite (RPi26 25%nat) by inl; exact R25_25).
    assert (R26_26: getr R26 (reg 26) = Z_to_bv 64 w560) by (rewrite (RPi26 26%nat) by inl; exact R25_26).
    assert (R26_27: getr R26 (reg 27) = Z_to_bv 64 w568) by (rewrite (RPi26 27%nat) by inl; exact R25_27).
    assert (c26_Sm56: L5.u64_at RSEGS M26 (S - 56) 138528) by (clear - AGS26 c25_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm56]).
    assert (c26_Sm64: L5.u64_at RSEGS M26 (S - 64) (S + 64)) by (clear - AGS26 c25_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm64]).
    assert (c26_Sm72: L5.u64_at RSEGS M26 (S - 72) (U R0 9)) by (clear - AGS26 c25_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm72]).
    assert (c26_Sm80: L5.u64_at RSEGS M26 (S - 80) (U R0 18)) by (clear - AGS26 c25_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm80]).
    assert (c26_Sm88: L5.u64_at RSEGS M26 (S - 88) (U R0 19)) by (clear - AGS26 c25_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm88]).
    assert (c26_Sm96: L5.u64_at RSEGS M26 (S - 96) (U R0 20)) by (clear - AGS26 c25_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm96]).
    assert (c26_Sm104: L5.u64_at RSEGS M26 (S - 104) (U R0 21)) by (clear - AGS26 c25_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm104]).
    assert (c26_Sm112: L5.u64_at RSEGS M26 (S - 112) (U R0 22)) by (clear - AGS26 c25_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm112]).
    assert (c26_Sm120: L5.u64_at RSEGS M26 (S - 120) (U R0 23)) by (clear - AGS26 c25_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm120]).
    assert (c26_Sm128: L5.u64_at RSEGS M26 (S - 128) (U R0 24)) by (clear - AGS26 c25_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm128]).
    assert (c26_Sm136: L5.u64_at RSEGS M26 (S - 136) (U R0 25)) by (clear - AGS26 c25_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm136]).
    assert (c26_Sm144: L5.u64_at RSEGS M26 (S - 144) (U R0 26)) by (clear - AGS26 c25_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm144]).
    assert (c26_Sm152: L5.u64_at RSEGS M26 (S - 152) (U R0 27)) by (clear - AGS26 c25_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm152]).
    assert (c26_Sm8: L5.u64_at RSEGS M26 (S - 8) 132608) by (clear - AGS26 c25_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm8]).
    assert (c26_Sm16: L5.u64_at RSEGS M26 (S - 16) (U R0 8)) by (clear - AGS26 c25_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm16]).
    assert (c26_Sm280w1: L5.u8_at RSEGS M26 (S - 280) fb280) by (clear - AGS26 c25_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M25 M26 _ _ _ (AGS26 _ 1)); [lia | exact c25_Sm280w1]).
    assert (c26_Sm248w1: L5.u8_at RSEGS M26 (S - 248) fb248) by (clear - AGS26 c25_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M25 M26 _ _ _ (AGS26 _ 1)); [lia | exact c25_Sm248w1]).
    assert (c26_Sm216w1: L5.u8_at RSEGS M26 (S - 216) fb216) by (clear - AGS26 c25_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M25 M26 _ _ _ (AGS26 _ 1)); [lia | exact c25_Sm216w1]).
    assert (c26_Sm192: L5.u64_at RSEGS M26 (S - 192) d3) by (clear - AGS26 c25_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm192]).
    assert (c26_Sm200: L5.u64_at RSEGS M26 (S - 200) 8) by (clear - AGS26 c25_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm200]).
    assert (c26_Sm184w1: L5.u8_at RSEGS M26 (S - 184) fb184) by (clear - AGS26 c25_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M25 M26 _ _ _ (AGS26 _ 1)); [lia | exact c25_Sm184w1]).
    assert (c26_Sm160: L5.u64_at RSEGS M26 (S - 160) d4) by (clear - AGS26 c25_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm160]).
    assert (c26_Sm168: L5.u64_at RSEGS M26 (S - 168) 8) by (clear - AGS26 c25_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M25 M26 _ _ _ (AGS26 _ 8)); [lia | exact c25_Sm168]).
    assert (c26_Sm48w1: L5.u8_at RSEGS M26 (S - 48) fb48) by (clear - AGS26 c25_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M25 M26 _ _ _ (AGS26 _ 1)); [lia | exact c25_Sm48w1]).
    assert (c26_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M26 (A + i) 0)) by (clear - AGB26_A c25_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB26_A); [lia | apply c25_Om128z8; exact Hi]).
    assert (c26_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M26 ((A + 48) + i) 0)) by (clear - AGB26_A c25_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB26_A); [lia | apply c25_Om80z12; exact Hi]).
    assert (c26_Op0: L5.u64_at RSEGS M26 (A + 128) 373272) by (clear - AGB26_A c25_Op0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Op0]).
    assert (c26_Op8: L5.u64_at RSEGS M26 (A + 136) (ref + 24)) by (clear - AGB26_A c25_Op8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Op8]).
    assert (c26_Fp24: L5.u64_at RSEGS M26 (ref + 24) 8028075845441778529) by (clear - AGB26_ref c25_Fp24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp24]).
    assert (c26_Fp32: L5.u64_at RSEGS M26 (ref + 32) 7863351059373564014) by (clear - AGB26_ref c25_Fp32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp32]).
    assert (c26_Fp40: L5.u64_at RSEGS M26 (ref + 40) 2838809733452757089) by (clear - AGB26_ref c25_Fp40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp40]).
    assert (c26_Fp48: L5.u64_at RSEGS M26 (ref + 48) 2334102023183623712) by (clear - AGB26_ref c25_Fp48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp48]).
    assert (c26_Fp56: L5.u64_at RSEGS M26 (ref + 56) 4188416081412519009) by (clear - AGB26_ref c25_Fp56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp56]).
    assert (c26_Fp64w1: L5.u8_at RSEGS M26 (ref + 64) 48) by (clear - AGB26_ref c25_Fp64w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp64w1]).
    assert (c26_Fp65w1: L5.u8_at RSEGS M26 (ref + 65) 0) by (clear - AGB26_ref c25_Fp65w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb8 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp65w1]).
    assert (c26_Fp16w4: L5.u32_at RSEGS M26 (ref + 16) 0) by (clear - AGB26_ref c25_Fp16w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb32 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp16w4]).
    assert (c26_Fp8: L5.u64_at RSEGS M26 (ref + 8) 41) by (clear - AGB26_ref c25_Fp8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp8]).
    assert (c26_Fp0: L5.u64_at RSEGS M26 ref 41) by (clear - AGB26_ref c25_Fp0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_ref B1_ref B3_ref B4_ref; eapply (trb64 _ _ _ _ _ _ AGB26_ref); [lia | exact c25_Fp0]).
    assert (c26_Om8: L5.u64_at RSEGS M26 (A + 120) S) by (clear - AGB26_A c25_Om8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om8]).
    assert (c26_Om40: L5.u64_at RSEGS M26 (A + 88) (A + 128)) by (clear - AGB26_A c25_Om40 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om40]).
    assert (c26_Om48: L5.u64_at RSEGS M26 (A + 80) 133016) by (clear - AGB26_A c25_Om48 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om48]).
    assert (c26_Om56: L5.u64_at RSEGS M26 (A + 72) 91560) by (clear - AGB26_A c25_Om56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om56]).
    assert (c26_Om64: L5.u64_at RSEGS M26 (A + 64) 91699) by (clear - AGB26_A c25_Om64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om64]).
    assert (c26_Om68w4: L5.u32_at RSEGS M26 (A + 60) 1) by (clear - AGB26_A c25_Om68w4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb32 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om68w4]).
    assert (c26_Om16: L5.u64_at RSEGS M26 (A + 112) 0) by (clear - AGB26_A c25_Om16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om16]).
    assert (c26_Om120: L5.u64_at RSEGS M26 (A + 8) 1) by (clear - AGB26_A c25_Om120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om120]).
    assert (c26_Om24: L5.u64_at RSEGS M26 (A + 104) 257624) by (clear - AGB26_A c25_Om24 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om24]).
    assert (c26_Om32: L5.u64_at RSEGS M26 (A + 96) 4849336966747728640) by (clear - AGB26_A c25_Om32 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om32]).
    assert (c26_Om88: L5.u64_at RSEGS M26 (A + 40) 142700) by (clear - AGB26_A c25_Om88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om88]).
    assert (c26_Om104: L5.u64_at RSEGS M26 (A + 24) 253816) by (clear - AGB26_A c25_Om104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om104]).
    assert (c26_Om112: L5.u64_at RSEGS M26 (A + 16) 373232) by (clear - AGB26_A c25_Om112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om112]).
    assert (c26_Om96: L5.u64_at RSEGS M26 (A + 32) 142968) by (clear - AGB26_A c25_Om96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (trb64 _ _ _ _ _ _ AGB26_A); [lia | exact c25_Om96]).
    assert (HQ26: L5C.hpres L LB1 S 10240 XSF M M26).
    { clear - LBWF HQ25 HP26 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((ref, 66) :: (A, 144) :: (d4, 64) :: LB1) S 10240 XSF (S - 352) 8224 [] M M25 M26). exact LBWF. lia. lia. exact HQ25. exact HP26. intros bb Hbb; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS26 STAT26 PRES26 RP26 RPi26 HP26 AGB26_ref AGB26_A AGB26_d4.
    try clear c25_Sm56 c25_Sm64 c25_Sm72 c25_Sm80 c25_Sm88 c25_Sm96 c25_Sm104 c25_Sm112 c25_Sm120 c25_Sm128 c25_Sm136 c25_Sm144 c25_Sm152 c25_Sm8 c25_Sm16 c25_Sm280w1 c25_Sm248w1 c25_Sm216w1 c25_Sm192 c25_Sm200 c25_Sm184w1 c25_Sm160 c25_Sm168 c25_Sm48w1 c25_Om128z8 c25_Om80z12 c25_Op0 c25_Op8 c25_Fp24 c25_Fp32 c25_Fp40 c25_Fp48 c25_Fp56 c25_Fp64w1 c25_Fp65w1 c25_Fp16w4 c25_Fp8 c25_Fp0 c25_Om8 c25_Om40 c25_Om48 c25_Om56 c25_Om64 c25_Om68w4 c25_Om16 c25_Om120 c25_Om24 c25_Om32 c25_Om88 c25_Om104 c25_Om112 c25_Om96 R25_1 R25_2 R25_3 R25_4 R25_8 R25_9 R25_10 R25_11 R25_18 R25_19 R25_20 R25_21 R25_22 R25_23 R25_24 R25_25 R25_26 R25_27 DEF25 HH25 HQ25 ES25 K25 DEFref_25 DEFA_25 DEFd3_25 DEFd4_25.
    eapply (seg15 fx25 R0 R R26 M M26 model model26 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A ref HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R26_2 R26_3 R26_4 R26_8 R26_9 R26_18 R26_19 R26_20 R26_21 R26_22 R26_23 R26_24 R26_25 R26_26 R26_27 c26_Sm56 c26_Sm64 c26_Sm72 c26_Sm80 c26_Sm88 c26_Sm96 c26_Sm104 c26_Sm112 c26_Sm120 c26_Sm128 c26_Sm136 c26_Sm144 c26_Sm152 c26_Sm8 c26_Sm16 c26_Sm280w1 c26_Sm248w1 c26_Sm216w1 c26_Sm192 c26_Sm200 c26_Sm184w1 c26_Sm160 c26_Sm168 c26_Sm48w1 c26_Om128z8 c26_Om80z12 c26_Op0 c26_Op8 c26_Fp24 c26_Fp32 c26_Fp40 c26_Fp48 c26_Fp56 c26_Fp64w1 c26_Fp65w1 c26_Fp16w4 c26_Fp8 c26_Fp0 c26_Om8 c26_Om40 c26_Om48 c26_Om56 c26_Om64 c26_Om68w4 c26_Om16 c26_Om120 c26_Om24 c26_Om32 c26_Om88 c26_Om104 c26_Om112 c26_Om96 ES26 DEF26 DEFref_26 DEFA_26 DEFd4_26 BR_ref BR_A BR_d4 AP_ref_A AP_ref_d4 AP_A_d4 FRSH_ref FRSH_A HH26 MOK26 MBV26 HQ26 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S14.
