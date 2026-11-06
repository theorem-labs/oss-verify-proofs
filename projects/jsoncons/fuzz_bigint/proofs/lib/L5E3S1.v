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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S1.
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
Let seg2 := L5E3S2.seg2 L HI LY LYX HIok.

Lemma seg1 (fx : FPState) (R0 R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 : Z) :
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
  (* [comment removed for export] *) getr R (reg 2) = Z_to_bv 64 (S - 896) ->
  (* [comment removed for export] *) getr R (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R (reg 8) = Z_to_bv 64 (S + 64) ->
  (* [comment removed for export] *) getr R (reg 10) = Z_to_bv 64 16 ->
  (* [comment removed for export] *) getr R (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M (S - 48) fb48 ->
  (* [comment removed for export] *) e1_statics M gd fl av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M d1 64 ->
  (* [comment removed for export] *) L5.defined M d2 64 ->
  (* [comment removed for export] *) L5.defined M d3 64 ->
  (* [comment removed for export] *) L5.defined M d4 64 ->
  (* [comment removed for export] *) block_range L d1 64 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
  (* [comment removed for export] *) (d1 + 64 <= d2 \/ d2 + 64 <= d1) ->
  (* [comment removed for export] *) (d1 + 64 <= d3 \/ d3 + 64 <= d1) ->
  (* [comment removed for export] *) (d1 + 64 <= d4 \/ d4 + 64 <= d1) ->
  (* [comment removed for export] *) (d2 + 64 <= d3 \/ d3 + 64 <= d2) ->
  (* [comment removed for export] *) (d2 + 64 <= d4 \/ d4 + 64 <= d2) ->
  (* [comment removed for export] *) (d3 + 64 <= d4 \/ d4 + 64 <= d3) ->
  (* [comment removed for export] *) hi_heap HI ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (cr) M (m_vmmaps model) ->
  (* [comment removed for export] *) model_ok model ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx R 136304 M model) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 R0_2 R0_3 R0_4 R0_8 R0_10 R0_20 c0_Sm840 c0_Sm848 c0_Sm856 c0_Sm864 c0_Sm872 c0_Sm776 c0_Sm784 c0_Sm792 c0_Sm800 c0_Sm472 c0_Sm480 c0_Sm488 c0_Sm496 c0_Sm504 c0_Sm512 c0_Sm520 c0_Sm528 c0_Sm536 c0_Sm544 c0_Sm552 c0_Sm560 c0_Sm568 c0_Sm424 c0_Sm432 c0_Sm360 c0_Sm368 c0_Sm376 c0_Sm56 c0_Sm64 c0_Sm72 c0_Sm80 c0_Sm88 c0_Sm96 c0_Sm104 c0_Sm112 c0_Sm120 c0_Sm128 c0_Sm136 c0_Sm144 c0_Sm152 c0_Sm8 c0_Sm16 c0_Sm696w1 c0_Sm664w1 c0_Sm640 c0_Sm648 c0_Sm632w1 c0_Sm608 c0_Sm616 c0_Sm600w1 c0_Sm464w1 c0_Sm408w1 c0_Sm280w1 c0_Sm248w1 c0_Sm216w1 c0_Sm192 c0_Sm200 c0_Sm184w1 c0_Sm160 c0_Sm168 c0_Sm48w1 ES0 DEF0 DEFd1_0 DEFd2_0 DEFd3_0 DEFd4_0 BR_d1 BR_d2 BR_d3 BR_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 HH0 MOK0 HQ0 KE.
  pose proof MOK0 as (Mh & Ml & Mm).
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (FAKE16: (S - 1168) mod 16 = 0). { clear - A16. replace (S - 1168) with (S + (-73) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES0 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9.
  pose proof (auxv_cells M av uid rnd hw S_13) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  assert (WUW: L5.writable RSEGS M 459617 6). { apply (writable_img M UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; kl. }
  assert (WUC: L5.writable RSEGS M 456960 4). { apply (writable_img M EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; kl. }
  unshelve epose proof (e3a1_conc fx R M (S - 896) (S - 1168) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx1 & R1 & M1 & MS1 & K1 & R1_1 & R1_2 & R1_8 & R1_10 & R1_11 & C1_0 & C1_1 & C1_2 & C1_3 & C1_4 & FR1 & GR1).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF0); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF0); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF0); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF0 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF0); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  assert (AG1: forall a k, ((a + k <= (S - 1008) \/ (S - 896) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M M1 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR1; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R1_1n: getr R1 (reg 1) = Z_to_bv 64 259044) by (rewrite R1_1; f_equal; ring). clear R1_1. rename R1_1n into R1_1.
  assert (R1_2n: getr R1 (reg 2) = Z_to_bv 64 (S - 944)) by (rewrite R1_2; f_equal; ring). clear R1_2. rename R1_2n into R1_2.
  assert (R1_3: getr R1 (reg 3) = Z_to_bv 64 67584) by (kin K1 3%nat; exact R0_3).
  assert (R1_4: getr R1 (reg 4) = Z_to_bv 64 459832) by (kin K1 4%nat; exact R0_4).
  assert (R1_8n: getr R1 (reg 8) = Z_to_bv 64 144) by (rewrite R1_8; f_equal; ring). clear R1_8. rename R1_8n into R1_8.
  assert (R1_10n: getr R1 (reg 10) = Z_to_bv 64 16) by (rewrite R1_10; f_equal; ring). clear R1_10. rename R1_10n into R1_10.
  assert (R1_11n: getr R1 (reg 11) = Z_to_bv 64 144) by (rewrite R1_11; f_equal; ring). clear R1_11. rename R1_11n into R1_11.
  assert (R1_20: getr R1 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K1 20%nat; exact R0_20).
  assert (c1_Sm840: L5.u64_at RSEGS M1 (S - 840) 135392) by (clear - AG1 c0_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm840]).
  assert (c1_Sm848: L5.u64_at RSEGS M1 (S - 848) (S + 64)) by (clear - AG1 c0_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm848]).
  assert (c1_Sm856: L5.u64_at RSEGS M1 (S - 856) w856) by (clear - AG1 c0_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm856]).
  assert (c1_Sm864: L5.u64_at RSEGS M1 (S - 864) w864) by (clear - AG1 c0_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm864]).
  assert (c1_Sm872: L5.u64_at RSEGS M1 (S - 872) w872) by (clear - AG1 c0_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm872]).
  assert (c1_Sm776: L5.u64_at RSEGS M1 (S - 776) 139520) by (clear - AG1 c0_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm776]).
  assert (c1_Sm784: L5.u64_at RSEGS M1 (S - 784) w784) by (clear - AG1 c0_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm784]).
  assert (c1_Sm792: L5.u64_at RSEGS M1 (S - 792) (S + 64)) by (clear - AG1 c0_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm792]).
  assert (c1_Sm800: L5.u64_at RSEGS M1 (S - 800) (S + 64)) by (clear - AG1 c0_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm800]).
  assert (c1_Sm472: L5.u64_at RSEGS M1 (S - 472) 142136) by (clear - AG1 c0_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm472]).
  assert (c1_Sm480: L5.u64_at RSEGS M1 (S - 480) (S + 64)) by (clear - AG1 c0_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm480]).
  assert (c1_Sm488: L5.u64_at RSEGS M1 (S - 488) w488) by (clear - AG1 c0_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm488]).
  assert (c1_Sm496: L5.u64_at RSEGS M1 (S - 496) (S + 64)) by (clear - AG1 c0_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm496]).
  assert (c1_Sm504: L5.u64_at RSEGS M1 (S - 504) w504) by (clear - AG1 c0_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm504]).
  assert (c1_Sm512: L5.u64_at RSEGS M1 (S - 512) w512) by (clear - AG1 c0_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm512]).
  assert (c1_Sm520: L5.u64_at RSEGS M1 (S - 520) w520) by (clear - AG1 c0_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm520]).
  assert (c1_Sm528: L5.u64_at RSEGS M1 (S - 528) w528) by (clear - AG1 c0_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm528]).
  assert (c1_Sm536: L5.u64_at RSEGS M1 (S - 536) w536) by (clear - AG1 c0_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm536]).
  assert (c1_Sm544: L5.u64_at RSEGS M1 (S - 544) w544) by (clear - AG1 c0_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm544]).
  assert (c1_Sm552: L5.u64_at RSEGS M1 (S - 552) w552) by (clear - AG1 c0_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm552]).
  assert (c1_Sm560: L5.u64_at RSEGS M1 (S - 560) w560) by (clear - AG1 c0_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm560]).
  assert (c1_Sm568: L5.u64_at RSEGS M1 (S - 568) w568) by (clear - AG1 c0_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm568]).
  assert (c1_Sm424: L5.u64_at RSEGS M1 (S - 424) 141264) by (clear - AG1 c0_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm424]).
  assert (c1_Sm432: L5.u64_at RSEGS M1 (S - 432) (S + 64)) by (clear - AG1 c0_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm432]).
  assert (c1_Sm360: L5.u64_at RSEGS M1 (S - 360) 139904) by (clear - AG1 c0_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm360]).
  assert (c1_Sm368: L5.u64_at RSEGS M1 (S - 368) (S + 64)) by (clear - AG1 c0_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm368]).
  assert (c1_Sm376: L5.u64_at RSEGS M1 (S - 376) (S - 48)) by (clear - AG1 c0_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm376]).
  assert (c1_Sm56: L5.u64_at RSEGS M1 (S - 56) 138528) by (clear - AG1 c0_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm56]).
  assert (c1_Sm64: L5.u64_at RSEGS M1 (S - 64) (S + 64)) by (clear - AG1 c0_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm64]).
  assert (c1_Sm72: L5.u64_at RSEGS M1 (S - 72) (U R0 9)) by (clear - AG1 c0_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm72]).
  assert (c1_Sm80: L5.u64_at RSEGS M1 (S - 80) (U R0 18)) by (clear - AG1 c0_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm80]).
  assert (c1_Sm88: L5.u64_at RSEGS M1 (S - 88) (U R0 19)) by (clear - AG1 c0_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm88]).
  assert (c1_Sm96: L5.u64_at RSEGS M1 (S - 96) (U R0 20)) by (clear - AG1 c0_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm96]).
  assert (c1_Sm104: L5.u64_at RSEGS M1 (S - 104) (U R0 21)) by (clear - AG1 c0_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm104]).
  assert (c1_Sm112: L5.u64_at RSEGS M1 (S - 112) (U R0 22)) by (clear - AG1 c0_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm112]).
  assert (c1_Sm120: L5.u64_at RSEGS M1 (S - 120) (U R0 23)) by (clear - AG1 c0_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm120]).
  assert (c1_Sm128: L5.u64_at RSEGS M1 (S - 128) (U R0 24)) by (clear - AG1 c0_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm128]).
  assert (c1_Sm136: L5.u64_at RSEGS M1 (S - 136) (U R0 25)) by (clear - AG1 c0_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm136]).
  assert (c1_Sm144: L5.u64_at RSEGS M1 (S - 144) (U R0 26)) by (clear - AG1 c0_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm144]).
  assert (c1_Sm152: L5.u64_at RSEGS M1 (S - 152) (U R0 27)) by (clear - AG1 c0_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm152]).
  assert (c1_Sm8: L5.u64_at RSEGS M1 (S - 8) 132608) by (clear - AG1 c0_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm8]).
  assert (c1_Sm16: L5.u64_at RSEGS M1 (S - 16) (U R0 8)) by (clear - AG1 c0_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm16]).
  assert (c1_Sm696w1: L5.u8_at RSEGS M1 (S - 696) fb696) by (clear - AG1 c0_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm696w1]).
  assert (c1_Sm664w1: L5.u8_at RSEGS M1 (S - 664) fb664) by (clear - AG1 c0_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm664w1]).
  assert (c1_Sm640: L5.u64_at RSEGS M1 (S - 640) d1) by (clear - AG1 c0_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm640]).
  assert (c1_Sm648: L5.u64_at RSEGS M1 (S - 648) 8) by (clear - AG1 c0_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm648]).
  assert (c1_Sm632w1: L5.u8_at RSEGS M1 (S - 632) fb632) by (clear - AG1 c0_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm632w1]).
  assert (c1_Sm608: L5.u64_at RSEGS M1 (S - 608) d2) by (clear - AG1 c0_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm608]).
  assert (c1_Sm616: L5.u64_at RSEGS M1 (S - 616) 8) by (clear - AG1 c0_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm616]).
  assert (c1_Sm600w1: L5.u8_at RSEGS M1 (S - 600) fb600) by (clear - AG1 c0_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm600w1]).
  assert (c1_Sm464w1: L5.u8_at RSEGS M1 (S - 464) fb464) by (clear - AG1 c0_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm464w1]).
  assert (c1_Sm408w1: L5.u8_at RSEGS M1 (S - 408) fb408) by (clear - AG1 c0_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm408w1]).
  assert (c1_Sm280w1: L5.u8_at RSEGS M1 (S - 280) fb280) by (clear - AG1 c0_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm280w1]).
  assert (c1_Sm248w1: L5.u8_at RSEGS M1 (S - 248) fb248) by (clear - AG1 c0_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm248w1]).
  assert (c1_Sm216w1: L5.u8_at RSEGS M1 (S - 216) fb216) by (clear - AG1 c0_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm216w1]).
  assert (c1_Sm192: L5.u64_at RSEGS M1 (S - 192) d3) by (clear - AG1 c0_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm192]).
  assert (c1_Sm200: L5.u64_at RSEGS M1 (S - 200) 8) by (clear - AG1 c0_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm200]).
  assert (c1_Sm184w1: L5.u8_at RSEGS M1 (S - 184) fb184) by (clear - AG1 c0_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm184w1]).
  assert (c1_Sm160: L5.u64_at RSEGS M1 (S - 160) d4) by (clear - AG1 c0_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm160]).
  assert (c1_Sm168: L5.u64_at RSEGS M1 (S - 168) 8) by (clear - AG1 c0_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M M1 _ _ _ (AG1 _ 8)); [lia | exact c0_Sm168]).
  assert (c1_Sm48w1: L5.u8_at RSEGS M1 (S - 48) fb48) by (clear - AG1 c0_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M M1 _ _ _ (AG1 _ 1)); [lia | exact c0_Sm48w1]).
  assert (c1_Sm944: L5.u64_at RSEGS M1 (S - 944) 144) by (cellfix C1_0). clear C1_0.
  assert (c1_Sm936: L5.u64_at RSEGS M1 (S - 936) 257240) by (cellfix C1_1). clear C1_1.
  set (u0_9 := U R 9). assert (Wu0_9: 0 <= u0_9 < 2 ^ 64) by (unfold u0_9, U; apply wrange).
  assert (R0_9: getr R (reg 9) = Z_to_bv 64 u0_9) by (unfold u0_9, U; symmetry; apply lit_of_word). clearbody u0_9.
  rewrite R0_9, BG.unsigned_lit in C1_2 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu0_9).
  assert (c1_Sm920: L5.u64_at RSEGS M1 (S - 920) u0_9) by (cellfix C1_2). clear C1_2.
  rewrite R0_8, BG.unsigned_lit in C1_3 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI).
  assert (c1_Sm912: L5.u64_at RSEGS M1 (S - 912) (S + 64)) by (cellfix C1_3). clear C1_3.
  assert (c1_Sm904: L5.u64_at RSEGS M1 (S - 904) 136308) by (cellfix C1_4). clear C1_4.
  assert (STAT1: forall a, stat_rd av a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { clear - FR1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (e1_statics_keep M M1 gd fl av uid rnd canary hw ES0 STAT1) as ES1.
  assert (DEF1: L5.defined M1 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR1 | exact DEF0]).
  assert (DEFd1_1: L5.defined M1 d1 64) by (eapply L5.defined_grows; [exact GR1 | exact DEFd1_0]).
  assert (DEFd2_1: L5.defined M1 d2 64) by (eapply L5.defined_grows; [exact GR1 | exact DEFd2_0]).
  assert (DEFd3_1: L5.defined M1 d3 64) by (eapply L5.defined_grows; [exact GR1 | exact DEFd3_0]).
  assert (DEFd4_1: L5.defined M1 d4 64) by (eapply L5.defined_grows; [exact GR1 | exact DEFd4_0]).
  assert (HH1: hi_heap HI ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (cr) M1 (m_vmmaps model)).
  { clear - HH0 GR1 FR1 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH0. lia. 2: exact GR1. intros a Ha.
    destruct (in_dec (S - 1008) (S - 896) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR1; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ1: L5C.hpres L LB1 S 10240 XSF M M1).
  { clear - LBWF HQ0 FR1 GR1 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M M1 [((S - 1008), 112)]). exact LBWF. lia. exact HQ0.
    { intros x Hx. apply FR1; intros Hin.
        apply (Hx ((S - 1008), 112)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR1.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  assert (R1_9: getr R1 (reg 9) = Z_to_bv 64 u0_9) by (kin K1 9%nat; exact R0_9).
  clear AG1 FR1 MS1. try clear STAT1.
  try clear c0_Sm840. try clear c0_Sm848. try clear c0_Sm856. try clear c0_Sm864. try clear c0_Sm872. try clear c0_Sm776. try clear c0_Sm784. try clear c0_Sm792. try clear c0_Sm800. try clear c0_Sm472. try clear c0_Sm480. try clear c0_Sm488. try clear c0_Sm496. try clear c0_Sm504. try clear c0_Sm512. try clear c0_Sm520. try clear c0_Sm528. try clear c0_Sm536. try clear c0_Sm544. try clear c0_Sm552. try clear c0_Sm560. try clear c0_Sm568. try clear c0_Sm424. try clear c0_Sm432. try clear c0_Sm360. try clear c0_Sm368. try clear c0_Sm376. try clear c0_Sm56. try clear c0_Sm64. try clear c0_Sm72. try clear c0_Sm80. try clear c0_Sm88. try clear c0_Sm96. try clear c0_Sm104. try clear c0_Sm112. try clear c0_Sm120. try clear c0_Sm128. try clear c0_Sm136. try clear c0_Sm144. try clear c0_Sm152. try clear c0_Sm8. try clear c0_Sm16. try clear c0_Sm696w1. try clear c0_Sm664w1. try clear c0_Sm640. try clear c0_Sm648. try clear c0_Sm632w1. try clear c0_Sm608. try clear c0_Sm616. try clear c0_Sm600w1. try clear c0_Sm464w1. try clear c0_Sm408w1. try clear c0_Sm280w1. try clear c0_Sm248w1. try clear c0_Sm216w1. try clear c0_Sm192. try clear c0_Sm200. try clear c0_Sm184w1. try clear c0_Sm160. try clear c0_Sm168. try clear c0_Sm48w1. try clear R0_2. try clear R0_3. try clear R0_4. try clear R0_10. try clear R0_8. try clear R0_20. try clear R0_9. try clear DEF0. try clear HH0. try clear HQ0. try clear ES0. try clear DEFd1_0. try clear DEFd2_0. try clear DEFd3_0. try clear DEFd4_0.
  (* [comment removed for export] *)
  pose proof (hio_aligned L SCFG HI HIok fx1 R1 M1 model ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (cr) 144 K) as HC.
  rewrite (ly_segs L LY), (ly_aligned L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH1.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - rewrite L5CoreKit.L5K.rl10. exact R1_10.
  - rewrite L5CoreKit.L5K.rl11. exact R1_11.
  - kl.
  - exact CR144.
  - rewrite L5CoreKit.L5K.rl4. exact R1_4.
  - rewrite L5CoreKit.L5K.rl1, R1_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R1_2 A16 DEF1 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R1_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-59) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M1 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF1. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R2 M2 model2 A HA10 RP2 BRn BAn DEFn PRES2 MBVn HH2.
    rewrite L5CoreKit.L5K.rl1, R1_1.
    rewrite L5CoreKit.L5K.rl2, R1_2, BG.unsigned_lit in PRES2 by (kl SLO SHI STOP).
    match type of PRES2 with heap_pres_core _ _ ?x _ _ => replace x with (S - 944) in PRES2 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 944) M1 M2 PRES2) as HP2. rewrite (ly_stack L LY) in HP2. unfold HEAP_STACK in HP2.
    assert (AGS2: forall a k, ((S - 944) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M1 M2 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP2 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP2. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB2_d1: L5C.agree_on M1 M2 d1 64).
    { clear - HP2 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP2. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d1. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB2_d2: L5C.agree_on M1 M2 d2 64).
    { clear - HP2 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP2. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d2. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB2_d3: L5C.agree_on M1 M2 d3 64).
    { clear - HP2 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP2. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB2_d4: L5C.agree_on M1 M2 d4 64).
    { clear - HP2 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP2. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT2: forall a, stat_rd av a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { clear - HP2 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 944) 8224 [] M1 M2 HP2). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (e1_statics_keep M1 M2 gd fl av uid rnd canary hw ES1 STAT2) as ES2.
    assert (DEF2: L5.defined M2 (S - 10240) 10240).
    { clear - HP2 DEF1 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 944) 8224 [] M1 M2). exact HP2. lia. lia. lia. lia. exact DEF1. }
    assert (DEFd1_2: L5.defined M2 d1 64) by (eapply (L5C.defined_agree M1 M2); [exact AGB2_d1 | exact DEFd1_1]).
    assert (DEFd2_2: L5.defined M2 d2 64) by (eapply (L5C.defined_agree M1 M2); [exact AGB2_d2 | exact DEFd2_1]).
    assert (DEFd3_2: L5.defined M2 d3 64) by (eapply (L5C.defined_agree M1 M2); [exact AGB2_d3 | exact DEFd3_1]).
    assert (DEFd4_2: L5.defined M2 d4 64) by (eapply (L5C.defined_agree M1 M2); [exact AGB2_d4 | exact DEFd4_1]).
    assert (DEFA_2: L5.defined M2 A 144) by exact DEFn. clear DEFn.
    pose proof BRn as BR_A. clear BRn. pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
    pose proof (BAn (d1, 64) ltac:(left; reflexivity)) as AP_A_d1. cbn [fst snd] in AP_A_d1.
    pose proof (BAn (d2, 64) ltac:(right; left; reflexivity)) as AP_A_d2. cbn [fst snd] in AP_A_d2.
    pose proof (BAn (d3, 64) ltac:(right; right; left; reflexivity)) as AP_A_d3. cbn [fst snd] in AP_A_d3.
    pose proof (BAn (d4, 64) ltac:(right; right; right; left; reflexivity)) as AP_A_d4. cbn [fst snd] in AP_A_d4.
    assert (FRSH_A: L5PK.fresh_rng L LB1 A 144). { clear - BAn LY B0_A B1_A B3_A B4_A STOP. split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. split. lia. intros bb Hbb. apply BAn. right. right. right. right.  exact Hbb. }
    clear BAn.
    assert (MOK2: model_ok model2).
    { destruct MOK0 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK2 as (Mh & Ml & Mm).
    rename MBVn into MBV2.
    assert (RPi2: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg i) = getr R1 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R1 R2 i RP2). exact Hi. }
    assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (S - 944)) by (rewrite (RPi2 2%nat) by inl; exact R1_2).
    assert (R2_3: getr R2 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi2 3%nat) by inl; exact R1_3).
    assert (R2_4: getr R2 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi2 4%nat) by inl; exact R1_4).
    assert (R2_8: getr R2 (reg 8) = Z_to_bv 64 144) by (rewrite (RPi2 8%nat) by inl; exact R1_8).
    assert (R2_9: getr R2 (reg 9) = Z_to_bv 64 u0_9) by (rewrite (RPi2 9%nat) by inl; exact R1_9).
    assert (R2_20: getr R2 (reg 20) = Z_to_bv 64 (S - 584)) by (rewrite (RPi2 20%nat) by inl; exact R1_20).
    rewrite L5CoreKit.L5K.rl10 in HA10. rename HA10 into R2_10.
    assert (c2_Sm840: L5.u64_at RSEGS M2 (S - 840) 135392) by (clear - AGS2 c1_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm840]).
    assert (c2_Sm848: L5.u64_at RSEGS M2 (S - 848) (S + 64)) by (clear - AGS2 c1_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm848]).
    assert (c2_Sm856: L5.u64_at RSEGS M2 (S - 856) w856) by (clear - AGS2 c1_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm856]).
    assert (c2_Sm864: L5.u64_at RSEGS M2 (S - 864) w864) by (clear - AGS2 c1_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm864]).
    assert (c2_Sm872: L5.u64_at RSEGS M2 (S - 872) w872) by (clear - AGS2 c1_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm872]).
    assert (c2_Sm776: L5.u64_at RSEGS M2 (S - 776) 139520) by (clear - AGS2 c1_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm776]).
    assert (c2_Sm784: L5.u64_at RSEGS M2 (S - 784) w784) by (clear - AGS2 c1_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm784]).
    assert (c2_Sm792: L5.u64_at RSEGS M2 (S - 792) (S + 64)) by (clear - AGS2 c1_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm792]).
    assert (c2_Sm800: L5.u64_at RSEGS M2 (S - 800) (S + 64)) by (clear - AGS2 c1_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm800]).
    assert (c2_Sm472: L5.u64_at RSEGS M2 (S - 472) 142136) by (clear - AGS2 c1_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm472]).
    assert (c2_Sm480: L5.u64_at RSEGS M2 (S - 480) (S + 64)) by (clear - AGS2 c1_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm480]).
    assert (c2_Sm488: L5.u64_at RSEGS M2 (S - 488) w488) by (clear - AGS2 c1_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm488]).
    assert (c2_Sm496: L5.u64_at RSEGS M2 (S - 496) (S + 64)) by (clear - AGS2 c1_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm496]).
    assert (c2_Sm504: L5.u64_at RSEGS M2 (S - 504) w504) by (clear - AGS2 c1_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm504]).
    assert (c2_Sm512: L5.u64_at RSEGS M2 (S - 512) w512) by (clear - AGS2 c1_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm512]).
    assert (c2_Sm520: L5.u64_at RSEGS M2 (S - 520) w520) by (clear - AGS2 c1_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm520]).
    assert (c2_Sm528: L5.u64_at RSEGS M2 (S - 528) w528) by (clear - AGS2 c1_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm528]).
    assert (c2_Sm536: L5.u64_at RSEGS M2 (S - 536) w536) by (clear - AGS2 c1_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm536]).
    assert (c2_Sm544: L5.u64_at RSEGS M2 (S - 544) w544) by (clear - AGS2 c1_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm544]).
    assert (c2_Sm552: L5.u64_at RSEGS M2 (S - 552) w552) by (clear - AGS2 c1_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm552]).
    assert (c2_Sm560: L5.u64_at RSEGS M2 (S - 560) w560) by (clear - AGS2 c1_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm560]).
    assert (c2_Sm568: L5.u64_at RSEGS M2 (S - 568) w568) by (clear - AGS2 c1_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm568]).
    assert (c2_Sm424: L5.u64_at RSEGS M2 (S - 424) 141264) by (clear - AGS2 c1_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm424]).
    assert (c2_Sm432: L5.u64_at RSEGS M2 (S - 432) (S + 64)) by (clear - AGS2 c1_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm432]).
    assert (c2_Sm360: L5.u64_at RSEGS M2 (S - 360) 139904) by (clear - AGS2 c1_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm360]).
    assert (c2_Sm368: L5.u64_at RSEGS M2 (S - 368) (S + 64)) by (clear - AGS2 c1_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm368]).
    assert (c2_Sm376: L5.u64_at RSEGS M2 (S - 376) (S - 48)) by (clear - AGS2 c1_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm376]).
    assert (c2_Sm56: L5.u64_at RSEGS M2 (S - 56) 138528) by (clear - AGS2 c1_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm56]).
    assert (c2_Sm64: L5.u64_at RSEGS M2 (S - 64) (S + 64)) by (clear - AGS2 c1_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm64]).
    assert (c2_Sm72: L5.u64_at RSEGS M2 (S - 72) (U R0 9)) by (clear - AGS2 c1_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm72]).
    assert (c2_Sm80: L5.u64_at RSEGS M2 (S - 80) (U R0 18)) by (clear - AGS2 c1_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm80]).
    assert (c2_Sm88: L5.u64_at RSEGS M2 (S - 88) (U R0 19)) by (clear - AGS2 c1_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm88]).
    assert (c2_Sm96: L5.u64_at RSEGS M2 (S - 96) (U R0 20)) by (clear - AGS2 c1_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm96]).
    assert (c2_Sm104: L5.u64_at RSEGS M2 (S - 104) (U R0 21)) by (clear - AGS2 c1_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm104]).
    assert (c2_Sm112: L5.u64_at RSEGS M2 (S - 112) (U R0 22)) by (clear - AGS2 c1_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm112]).
    assert (c2_Sm120: L5.u64_at RSEGS M2 (S - 120) (U R0 23)) by (clear - AGS2 c1_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm120]).
    assert (c2_Sm128: L5.u64_at RSEGS M2 (S - 128) (U R0 24)) by (clear - AGS2 c1_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm128]).
    assert (c2_Sm136: L5.u64_at RSEGS M2 (S - 136) (U R0 25)) by (clear - AGS2 c1_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm136]).
    assert (c2_Sm144: L5.u64_at RSEGS M2 (S - 144) (U R0 26)) by (clear - AGS2 c1_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm144]).
    assert (c2_Sm152: L5.u64_at RSEGS M2 (S - 152) (U R0 27)) by (clear - AGS2 c1_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm152]).
    assert (c2_Sm8: L5.u64_at RSEGS M2 (S - 8) 132608) by (clear - AGS2 c1_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm8]).
    assert (c2_Sm16: L5.u64_at RSEGS M2 (S - 16) (U R0 8)) by (clear - AGS2 c1_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm16]).
    assert (c2_Sm696w1: L5.u8_at RSEGS M2 (S - 696) fb696) by (clear - AGS2 c1_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm696w1]).
    assert (c2_Sm664w1: L5.u8_at RSEGS M2 (S - 664) fb664) by (clear - AGS2 c1_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm664w1]).
    assert (c2_Sm640: L5.u64_at RSEGS M2 (S - 640) d1) by (clear - AGS2 c1_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm640]).
    assert (c2_Sm648: L5.u64_at RSEGS M2 (S - 648) 8) by (clear - AGS2 c1_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm648]).
    assert (c2_Sm632w1: L5.u8_at RSEGS M2 (S - 632) fb632) by (clear - AGS2 c1_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm632w1]).
    assert (c2_Sm608: L5.u64_at RSEGS M2 (S - 608) d2) by (clear - AGS2 c1_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm608]).
    assert (c2_Sm616: L5.u64_at RSEGS M2 (S - 616) 8) by (clear - AGS2 c1_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm616]).
    assert (c2_Sm600w1: L5.u8_at RSEGS M2 (S - 600) fb600) by (clear - AGS2 c1_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm600w1]).
    assert (c2_Sm464w1: L5.u8_at RSEGS M2 (S - 464) fb464) by (clear - AGS2 c1_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm464w1]).
    assert (c2_Sm408w1: L5.u8_at RSEGS M2 (S - 408) fb408) by (clear - AGS2 c1_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm408w1]).
    assert (c2_Sm280w1: L5.u8_at RSEGS M2 (S - 280) fb280) by (clear - AGS2 c1_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm280w1]).
    assert (c2_Sm248w1: L5.u8_at RSEGS M2 (S - 248) fb248) by (clear - AGS2 c1_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm248w1]).
    assert (c2_Sm216w1: L5.u8_at RSEGS M2 (S - 216) fb216) by (clear - AGS2 c1_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm216w1]).
    assert (c2_Sm192: L5.u64_at RSEGS M2 (S - 192) d3) by (clear - AGS2 c1_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm192]).
    assert (c2_Sm200: L5.u64_at RSEGS M2 (S - 200) 8) by (clear - AGS2 c1_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm200]).
    assert (c2_Sm184w1: L5.u8_at RSEGS M2 (S - 184) fb184) by (clear - AGS2 c1_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm184w1]).
    assert (c2_Sm160: L5.u64_at RSEGS M2 (S - 160) d4) by (clear - AGS2 c1_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm160]).
    assert (c2_Sm168: L5.u64_at RSEGS M2 (S - 168) 8) by (clear - AGS2 c1_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm168]).
    assert (c2_Sm48w1: L5.u8_at RSEGS M2 (S - 48) fb48) by (clear - AGS2 c1_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M1 M2 _ _ _ (AGS2 _ 1)); [lia | exact c1_Sm48w1]).
    assert (c2_Sm944: L5.u64_at RSEGS M2 (S - 944) 144) by (clear - AGS2 c1_Sm944 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm944]).
    assert (c2_Sm936: L5.u64_at RSEGS M2 (S - 936) 257240) by (clear - AGS2 c1_Sm936 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm936]).
    assert (c2_Sm920: L5.u64_at RSEGS M2 (S - 920) u0_9) by (clear - AGS2 c1_Sm920 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm920]).
    assert (c2_Sm912: L5.u64_at RSEGS M2 (S - 912) (S + 64)) by (clear - AGS2 c1_Sm912 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm912]).
    assert (c2_Sm904: L5.u64_at RSEGS M2 (S - 904) 136308) by (clear - AGS2 c1_Sm904 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M1 M2 _ _ _ (AGS2 _ 8)); [lia | exact c1_Sm904]).
    assert (HQ2: L5C.hpres L LB1 S 10240 XSF M M2).
    { clear - LBWF HQ1 HP2 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 944) 8224 [] M M1 M2). exact LBWF. lia. lia. exact HQ1. exact HP2. intros bb Hbb; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS2 STAT2 PRES2 RP2 RPi2 HP2 AGB2_d1 AGB2_d2 AGB2_d3 AGB2_d4.
    try clear c1_Sm840 c1_Sm848 c1_Sm856 c1_Sm864 c1_Sm872 c1_Sm776 c1_Sm784 c1_Sm792 c1_Sm800 c1_Sm472 c1_Sm480 c1_Sm488 c1_Sm496 c1_Sm504 c1_Sm512 c1_Sm520 c1_Sm528 c1_Sm536 c1_Sm544 c1_Sm552 c1_Sm560 c1_Sm568 c1_Sm424 c1_Sm432 c1_Sm360 c1_Sm368 c1_Sm376 c1_Sm56 c1_Sm64 c1_Sm72 c1_Sm80 c1_Sm88 c1_Sm96 c1_Sm104 c1_Sm112 c1_Sm120 c1_Sm128 c1_Sm136 c1_Sm144 c1_Sm152 c1_Sm8 c1_Sm16 c1_Sm696w1 c1_Sm664w1 c1_Sm640 c1_Sm648 c1_Sm632w1 c1_Sm608 c1_Sm616 c1_Sm600w1 c1_Sm464w1 c1_Sm408w1 c1_Sm280w1 c1_Sm248w1 c1_Sm216w1 c1_Sm192 c1_Sm200 c1_Sm184w1 c1_Sm160 c1_Sm168 c1_Sm48w1 c1_Sm944 c1_Sm936 c1_Sm920 c1_Sm912 c1_Sm904 R1_1 R1_2 R1_3 R1_4 R1_8 R1_10 R1_11 R1_20 R1_9 DEF1 HH1 HQ1 ES1 K1 DEFd1_1 DEFd2_1 DEFd3_1 DEFd4_1.
    eapply (seg2 fx1 R0 R R2 M M2 model model2 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A u0_9 HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 R2_2 R2_3 R2_4 R2_8 R2_9 R2_10 R2_20 c2_Sm840 c2_Sm848 c2_Sm856 c2_Sm864 c2_Sm872 c2_Sm776 c2_Sm784 c2_Sm792 c2_Sm800 c2_Sm472 c2_Sm480 c2_Sm488 c2_Sm496 c2_Sm504 c2_Sm512 c2_Sm520 c2_Sm528 c2_Sm536 c2_Sm544 c2_Sm552 c2_Sm560 c2_Sm568 c2_Sm424 c2_Sm432 c2_Sm360 c2_Sm368 c2_Sm376 c2_Sm56 c2_Sm64 c2_Sm72 c2_Sm80 c2_Sm88 c2_Sm96 c2_Sm104 c2_Sm112 c2_Sm120 c2_Sm128 c2_Sm136 c2_Sm144 c2_Sm152 c2_Sm8 c2_Sm16 c2_Sm696w1 c2_Sm664w1 c2_Sm640 c2_Sm648 c2_Sm632w1 c2_Sm608 c2_Sm616 c2_Sm600w1 c2_Sm464w1 c2_Sm408w1 c2_Sm280w1 c2_Sm248w1 c2_Sm216w1 c2_Sm192 c2_Sm200 c2_Sm184w1 c2_Sm160 c2_Sm168 c2_Sm48w1 c2_Sm944 c2_Sm936 c2_Sm920 c2_Sm912 c2_Sm904 ES2 DEF2 DEFA_2 DEFd1_2 DEFd2_2 DEFd3_2 DEFd4_2 BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_A HH2 MOK2 MBV2 HQ2 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S1.
