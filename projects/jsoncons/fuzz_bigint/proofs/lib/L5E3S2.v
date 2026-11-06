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
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3A L5E3T0 L5E3T1 L5E3P L5E3R1 L5E3R2 L5E3S3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5E3S2.
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
Let seg3 := L5E3S3.seg3 L HI LY LYX HIok.

Lemma seg2 (fx1 : FPState) (R0 R R2 : bvmap 5 word) (M M2 : word -> option byte) (model model2 : Model) (K : TSet)
      (LB1 : list (Z * Z)) (cr : credit) (gd fl : bool) (S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A u0_9 : Z) :
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
  (* [comment removed for export] *) getr R2 (reg 2) = Z_to_bv 64 (S - 944) ->
  (* [comment removed for export] *) getr R2 (reg 3) = Z_to_bv 64 67584 ->
  (* [comment removed for export] *) getr R2 (reg 4) = Z_to_bv 64 459832 ->
  (* [comment removed for export] *) getr R2 (reg 8) = Z_to_bv 64 144 ->
  (* [comment removed for export] *) getr R2 (reg 9) = Z_to_bv 64 u0_9 ->
  (* [comment removed for export] *) getr R2 (reg 10) = Z_to_bv 64 A ->
  (* [comment removed for export] *) getr R2 (reg 20) = Z_to_bv 64 (S - 584) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 840) 135392 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 848) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 856) w856 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 864) w864 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 872) w872 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 776) 139520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 784) w784 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 792) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 800) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 472) 142136 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 480) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 488) w488 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 496) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 504) w504 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 512) w512 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 520) w520 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 528) w528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 536) w536 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 544) w544 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 552) w552 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 560) w560 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 568) w568 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 424) 141264 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 432) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 360) 139904 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 368) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 376) (S - 48) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 56) 138528 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 64) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 72) (U R0 9) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 80) (U R0 18) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 88) (U R0 19) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 96) (U R0 20) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 104) (U R0 21) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 112) (U R0 22) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 120) (U R0 23) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 128) (U R0 24) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 136) (U R0 25) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 144) (U R0 26) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 152) (U R0 27) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 8) 132608 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 16) (U R0 8) ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 696) fb696 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 664) fb664 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 640) d1 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 648) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 632) fb632 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 608) d2 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 616) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 600) fb600 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 464) fb464 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 408) fb408 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 280) fb280 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 248) fb248 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 216) fb216 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 192) d3 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 200) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 184) fb184 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 160) d4 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 168) 8 ->
  (* [comment removed for export] *) L5.u8_at RSEGS M2 (S - 48) fb48 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 944) 144 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 936) 257240 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 920) u0_9 ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 912) (S + 64) ->
  (* [comment removed for export] *) L5.u64_at RSEGS M2 (S - 904) 136308 ->
  (* [comment removed for export] *) e1_statics M2 gd fl av uid rnd canary hw ->
  (* [comment removed for export] *) L5.defined M2 (S - 10240) 10240 ->
  (* [comment removed for export] *) L5.defined M2 A 144 ->
  (* [comment removed for export] *) L5.defined M2 d1 64 ->
  (* [comment removed for export] *) L5.defined M2 d2 64 ->
  (* [comment removed for export] *) L5.defined M2 d3 64 ->
  (* [comment removed for export] *) L5.defined M2 d4 64 ->
  (* [comment removed for export] *) block_range L A 144 ->
  (* [comment removed for export] *) block_range L d1 64 ->
  (* [comment removed for export] *) block_range L d2 64 ->
  (* [comment removed for export] *) block_range L d3 64 ->
  (* [comment removed for export] *) block_range L d4 64 ->
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
  (* [comment removed for export] *) L5PK.fresh_rng L LB1 A 144 ->
  (* [comment removed for export] *) hi_heap HI ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (cr) 144) M2 (m_vmmaps model2) ->
  (* [comment removed for export] *) model_ok model2 ->
  (* [comment removed for export] *) model_but_vm model model2 ->
  (* [comment removed for export] *) L5C.hpres L LB1 S 10240 XSF M M2 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
      regs_preserved R0 R' -> L5US.e3_landed L (L5US.xs_of gd fl av uid rnd canary hw) LB1 cr S M' R' LB' cr' ->
      L5C.hpres L LB1 S 10240 XSF M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@cfg fx' R' 133016 M' model') K) ->
  srealizes RSEGS SCFG (@cfg fx1 R2 259044 M2 model2) K.
Proof.
  intros HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 R2_2 R2_3 R2_4 R2_8 R2_9 R2_10 R2_20 c2_Sm840 c2_Sm848 c2_Sm856 c2_Sm864 c2_Sm872 c2_Sm776 c2_Sm784 c2_Sm792 c2_Sm800 c2_Sm472 c2_Sm480 c2_Sm488 c2_Sm496 c2_Sm504 c2_Sm512 c2_Sm520 c2_Sm528 c2_Sm536 c2_Sm544 c2_Sm552 c2_Sm560 c2_Sm568 c2_Sm424 c2_Sm432 c2_Sm360 c2_Sm368 c2_Sm376 c2_Sm56 c2_Sm64 c2_Sm72 c2_Sm80 c2_Sm88 c2_Sm96 c2_Sm104 c2_Sm112 c2_Sm120 c2_Sm128 c2_Sm136 c2_Sm144 c2_Sm152 c2_Sm8 c2_Sm16 c2_Sm696w1 c2_Sm664w1 c2_Sm640 c2_Sm648 c2_Sm632w1 c2_Sm608 c2_Sm616 c2_Sm600w1 c2_Sm464w1 c2_Sm408w1 c2_Sm280w1 c2_Sm248w1 c2_Sm216w1 c2_Sm192 c2_Sm200 c2_Sm184w1 c2_Sm160 c2_Sm168 c2_Sm48w1 c2_Sm944 c2_Sm936 c2_Sm920 c2_Sm912 c2_Sm904 ES2 DEF2 DEFA_2 DEFd1_2 DEFd2_2 DEFd3_2 DEFd4_2 BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_A HH2 MOK2 MBV2 HQ2 KE.
  pose proof MOK2 as (Mh & Ml & Mm).
  pose proof BR_A as (B0_A & B1_A & B2_A & B3_A & B4_A). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_A. unfold hl_ceil in B4_A.
  pose proof BR_d1 as (B0_d1 & B1_d1 & B2_d1 & B3_d1 & B4_d1). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d1. unfold hl_ceil in B4_d1.
  pose proof BR_d2 as (B0_d2 & B1_d2 & B2_d2 & B3_d2 & B4_d2). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d2. unfold hl_ceil in B4_d2.
  pose proof BR_d3 as (B0_d3 & B1_d3 & B2_d3 & B3_d3 & B4_d3). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d3. unfold hl_ceil in B4_d3.
  pose proof BR_d4 as (B0_d4 & B1_d4 & B2_d4 & B3_d4 & B4_d4). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_d4. unfold hl_ceil in B4_d4.
  pose proof ES2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVLO & AVHI & _).
  assert (CSP16: (S - 896) mod 16 = 0). { clear - A16. replace (S - 896) with (S + (-56) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
  assert (OBJ16: (A + 128) mod 16 = 0). { clear - B2_A. replace (A + 128) with (A + 8 * 16) by lia. rewrite Z_mod_plus_full. exact B2_A. }
  unfold cfg.
  (* [comment removed for export] *)
  pose proof ES2 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9.
  pose proof (auxv_cells M2 av uid rnd hw S_13) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  assert (WUW: L5.writable RSEGS M2 459617 6). { apply (writable_img M2 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; kl. }
  assert (WUC: L5.writable RSEGS M2 456960 4). { apply (writable_img M2 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; kl. }
  unshelve epose proof (e3a2_conc fx1 R2 M2 (S - 896) (A + 128) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx3 & R3 & M3 & MS3 & K3 & R3_1 & R3_2 & R3_8 & R3_10 & R3_11 & ZA3 & FR3 & GR3).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF2 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF2); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF2 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF2); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_2 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_2); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_2 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_2); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) first [exact c2_Sm936 | cellfix c2_Sm936]. }
  { (* [comment removed for export] *) first [exact c2_Sm944 | cellfix c2_Sm944]. }
  { (* [comment removed for export] *) first [exact c2_Sm904 | cellfix c2_Sm904]. }
  { (* [comment removed for export] *) first [exact c2_Sm912 | cellfix c2_Sm912]. }
  { (* [comment removed for export] *) rewrite R2_9, BG.unsigned_lit by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu0_9). first [exact c2_Sm920 | cellfix c2_Sm920]. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS3.
  (* [comment removed for export] *)
  assert (AG3: forall a k, ((a + k <= (S - 1008) \/ (S - 944) <= a) /\ (a + k <= A \/ (A + 144) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M2 M3 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & E1 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR3; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia | rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E1 Hi; lia]. }
  assert (R3_1n: getr R3 (reg 1) = Z_to_bv 64 136308) by (rewrite R3_1; f_equal; ring). clear R3_1. rename R3_1n into R3_1.
  assert (R3_2n: getr R3 (reg 2) = Z_to_bv 64 (S - 896)) by (rewrite R3_2; f_equal; ring). clear R3_2. rename R3_2n into R3_2.
  assert (R3_3: getr R3 (reg 3) = Z_to_bv 64 67584) by (kin K3 3%nat; exact R2_3).
  assert (R3_4: getr R3 (reg 4) = Z_to_bv 64 459832) by (kin K3 4%nat; exact R2_4).
  assert (R3_8n: getr R3 (reg 8) = Z_to_bv 64 (A + 128)) by (rewrite R3_8; f_equal; ring). clear R3_8. rename R3_8n into R3_8.
  assert (R3_9: getr R3 (reg 9) = Z_to_bv 64 u0_9) by (kin K3 9%nat; exact R2_9).
  assert (R3_10n: getr R3 (reg 10) = Z_to_bv 64 (S - 896)) by (rewrite R3_10; f_equal; ring). clear R3_10. rename R3_10n into R3_10.
  assert (R3_11n: getr R3 (reg 11) = Z_to_bv 64 74669) by (rewrite R3_11; f_equal; ring). clear R3_11. rename R3_11n into R3_11.
  assert (R3_20: getr R3 (reg 20) = Z_to_bv 64 (S - 584)) by (kin K3 20%nat; exact R2_20).
  assert (c3_Sm840: L5.u64_at RSEGS M3 (S - 840) 135392) by (clear - AG3 c2_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm840]).
  assert (c3_Sm848: L5.u64_at RSEGS M3 (S - 848) (S + 64)) by (clear - AG3 c2_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm848]).
  assert (c3_Sm856: L5.u64_at RSEGS M3 (S - 856) w856) by (clear - AG3 c2_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm856]).
  assert (c3_Sm864: L5.u64_at RSEGS M3 (S - 864) w864) by (clear - AG3 c2_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm864]).
  assert (c3_Sm872: L5.u64_at RSEGS M3 (S - 872) w872) by (clear - AG3 c2_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm872]).
  assert (c3_Sm776: L5.u64_at RSEGS M3 (S - 776) 139520) by (clear - AG3 c2_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm776]).
  assert (c3_Sm784: L5.u64_at RSEGS M3 (S - 784) w784) by (clear - AG3 c2_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm784]).
  assert (c3_Sm792: L5.u64_at RSEGS M3 (S - 792) (S + 64)) by (clear - AG3 c2_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm792]).
  assert (c3_Sm800: L5.u64_at RSEGS M3 (S - 800) (S + 64)) by (clear - AG3 c2_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm800]).
  assert (c3_Sm472: L5.u64_at RSEGS M3 (S - 472) 142136) by (clear - AG3 c2_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm472]).
  assert (c3_Sm480: L5.u64_at RSEGS M3 (S - 480) (S + 64)) by (clear - AG3 c2_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm480]).
  assert (c3_Sm488: L5.u64_at RSEGS M3 (S - 488) w488) by (clear - AG3 c2_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm488]).
  assert (c3_Sm496: L5.u64_at RSEGS M3 (S - 496) (S + 64)) by (clear - AG3 c2_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm496]).
  assert (c3_Sm504: L5.u64_at RSEGS M3 (S - 504) w504) by (clear - AG3 c2_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm504]).
  assert (c3_Sm512: L5.u64_at RSEGS M3 (S - 512) w512) by (clear - AG3 c2_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm512]).
  assert (c3_Sm520: L5.u64_at RSEGS M3 (S - 520) w520) by (clear - AG3 c2_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm520]).
  assert (c3_Sm528: L5.u64_at RSEGS M3 (S - 528) w528) by (clear - AG3 c2_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm528]).
  assert (c3_Sm536: L5.u64_at RSEGS M3 (S - 536) w536) by (clear - AG3 c2_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm536]).
  assert (c3_Sm544: L5.u64_at RSEGS M3 (S - 544) w544) by (clear - AG3 c2_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm544]).
  assert (c3_Sm552: L5.u64_at RSEGS M3 (S - 552) w552) by (clear - AG3 c2_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm552]).
  assert (c3_Sm560: L5.u64_at RSEGS M3 (S - 560) w560) by (clear - AG3 c2_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm560]).
  assert (c3_Sm568: L5.u64_at RSEGS M3 (S - 568) w568) by (clear - AG3 c2_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm568]).
  assert (c3_Sm424: L5.u64_at RSEGS M3 (S - 424) 141264) by (clear - AG3 c2_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm424]).
  assert (c3_Sm432: L5.u64_at RSEGS M3 (S - 432) (S + 64)) by (clear - AG3 c2_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm432]).
  assert (c3_Sm360: L5.u64_at RSEGS M3 (S - 360) 139904) by (clear - AG3 c2_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm360]).
  assert (c3_Sm368: L5.u64_at RSEGS M3 (S - 368) (S + 64)) by (clear - AG3 c2_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm368]).
  assert (c3_Sm376: L5.u64_at RSEGS M3 (S - 376) (S - 48)) by (clear - AG3 c2_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm376]).
  assert (c3_Sm56: L5.u64_at RSEGS M3 (S - 56) 138528) by (clear - AG3 c2_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm56]).
  assert (c3_Sm64: L5.u64_at RSEGS M3 (S - 64) (S + 64)) by (clear - AG3 c2_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm64]).
  assert (c3_Sm72: L5.u64_at RSEGS M3 (S - 72) (U R0 9)) by (clear - AG3 c2_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm72]).
  assert (c3_Sm80: L5.u64_at RSEGS M3 (S - 80) (U R0 18)) by (clear - AG3 c2_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm80]).
  assert (c3_Sm88: L5.u64_at RSEGS M3 (S - 88) (U R0 19)) by (clear - AG3 c2_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm88]).
  assert (c3_Sm96: L5.u64_at RSEGS M3 (S - 96) (U R0 20)) by (clear - AG3 c2_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm96]).
  assert (c3_Sm104: L5.u64_at RSEGS M3 (S - 104) (U R0 21)) by (clear - AG3 c2_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm104]).
  assert (c3_Sm112: L5.u64_at RSEGS M3 (S - 112) (U R0 22)) by (clear - AG3 c2_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm112]).
  assert (c3_Sm120: L5.u64_at RSEGS M3 (S - 120) (U R0 23)) by (clear - AG3 c2_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm120]).
  assert (c3_Sm128: L5.u64_at RSEGS M3 (S - 128) (U R0 24)) by (clear - AG3 c2_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm128]).
  assert (c3_Sm136: L5.u64_at RSEGS M3 (S - 136) (U R0 25)) by (clear - AG3 c2_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm136]).
  assert (c3_Sm144: L5.u64_at RSEGS M3 (S - 144) (U R0 26)) by (clear - AG3 c2_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm144]).
  assert (c3_Sm152: L5.u64_at RSEGS M3 (S - 152) (U R0 27)) by (clear - AG3 c2_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm152]).
  assert (c3_Sm8: L5.u64_at RSEGS M3 (S - 8) 132608) by (clear - AG3 c2_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm8]).
  assert (c3_Sm16: L5.u64_at RSEGS M3 (S - 16) (U R0 8)) by (clear - AG3 c2_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm16]).
  assert (c3_Sm696w1: L5.u8_at RSEGS M3 (S - 696) fb696) by (clear - AG3 c2_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm696w1]).
  assert (c3_Sm664w1: L5.u8_at RSEGS M3 (S - 664) fb664) by (clear - AG3 c2_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm664w1]).
  assert (c3_Sm640: L5.u64_at RSEGS M3 (S - 640) d1) by (clear - AG3 c2_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm640]).
  assert (c3_Sm648: L5.u64_at RSEGS M3 (S - 648) 8) by (clear - AG3 c2_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm648]).
  assert (c3_Sm632w1: L5.u8_at RSEGS M3 (S - 632) fb632) by (clear - AG3 c2_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm632w1]).
  assert (c3_Sm608: L5.u64_at RSEGS M3 (S - 608) d2) by (clear - AG3 c2_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm608]).
  assert (c3_Sm616: L5.u64_at RSEGS M3 (S - 616) 8) by (clear - AG3 c2_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm616]).
  assert (c3_Sm600w1: L5.u8_at RSEGS M3 (S - 600) fb600) by (clear - AG3 c2_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm600w1]).
  assert (c3_Sm464w1: L5.u8_at RSEGS M3 (S - 464) fb464) by (clear - AG3 c2_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm464w1]).
  assert (c3_Sm408w1: L5.u8_at RSEGS M3 (S - 408) fb408) by (clear - AG3 c2_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm408w1]).
  assert (c3_Sm280w1: L5.u8_at RSEGS M3 (S - 280) fb280) by (clear - AG3 c2_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm280w1]).
  assert (c3_Sm248w1: L5.u8_at RSEGS M3 (S - 248) fb248) by (clear - AG3 c2_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm248w1]).
  assert (c3_Sm216w1: L5.u8_at RSEGS M3 (S - 216) fb216) by (clear - AG3 c2_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm216w1]).
  assert (c3_Sm192: L5.u64_at RSEGS M3 (S - 192) d3) by (clear - AG3 c2_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm192]).
  assert (c3_Sm200: L5.u64_at RSEGS M3 (S - 200) 8) by (clear - AG3 c2_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm200]).
  assert (c3_Sm184w1: L5.u8_at RSEGS M3 (S - 184) fb184) by (clear - AG3 c2_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm184w1]).
  assert (c3_Sm160: L5.u64_at RSEGS M3 (S - 160) d4) by (clear - AG3 c2_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm160]).
  assert (c3_Sm168: L5.u64_at RSEGS M3 (S - 168) 8) by (clear - AG3 c2_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm168]).
  assert (c3_Sm48w1: L5.u8_at RSEGS M3 (S - 48) fb48) by (clear - AG3 c2_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr8 M2 M3 _ _ _ (AG3 _ 1)); [lia | exact c2_Sm48w1]).
  assert (c3_Sm944: L5.u64_at RSEGS M3 (S - 944) 144) by (clear - AG3 c2_Sm944 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm944]).
  assert (c3_Sm936: L5.u64_at RSEGS M3 (S - 936) 257240) by (clear - AG3 c2_Sm936 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm936]).
  assert (c3_Sm920: L5.u64_at RSEGS M3 (S - 920) u0_9) by (clear - AG3 c2_Sm920 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm920]).
  assert (c3_Sm912: L5.u64_at RSEGS M3 (S - 912) (S + 64)) by (clear - AG3 c2_Sm912 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm912]).
  assert (c3_Sm904: L5.u64_at RSEGS M3 (S - 904) 136308) by (clear - AG3 c2_Sm904 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; eapply (tr64 M2 M3 _ _ _ (AG3 _ 8)); [lia | exact c2_Sm904]).
  assert (STAT3: forall a, stat_rd av a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { clear - FR3 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR3; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (e1_statics_keep M2 M3 gd fl av uid rnd canary hw ES2 STAT3) as ES3.
  assert (DEF3: L5.defined M3 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR3 | exact DEF2]).
  assert (DEFA_3: L5.defined M3 A 144) by (eapply L5.defined_grows; [exact GR3 | exact DEFA_2]).
  assert (DEFd1_3: L5.defined M3 d1 64) by (eapply L5.defined_grows; [exact GR3 | exact DEFd1_2]).
  assert (DEFd2_3: L5.defined M3 d2 64) by (eapply L5.defined_grows; [exact GR3 | exact DEFd2_2]).
  assert (DEFd3_3: L5.defined M3 d3 64) by (eapply L5.defined_grows; [exact GR3 | exact DEFd3_2]).
  assert (DEFd4_3: L5.defined M3 d4 64) by (eapply L5.defined_grows; [exact GR3 | exact DEFd4_2]).
  assert (HH3: hi_heap HI ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (cr) 144) M3 (m_vmmaps model2)).
  { clear - HH2 GR3 FR3 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply hi_heap_clientx. exact HH2. lia. 2: exact GR3. intros a Ha.
    destruct (in_dec (S - 1008) (S - 944) a) as [IN0|OUT0]. { right; left; lia. }
    destruct (in_dec A (A + 144) a) as [IN1|OUT1]. { right; right; left; exists (A, 144); split; [left; reflexivity| cbn; lia]. }
    left; apply FR3; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ3: L5C.hpres L LB1 S 10240 XSF M M3).
  { clear - LBWF HQ2 FR3 GR3 IMGHI STOP ERR LY FRSH_A LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M2 M3 [((S - 1008), 64); (A, 144)]). exact LBWF. lia. exact HQ2.
    { intros x Hx. apply FR3; intros Hin.
      - apply (Hx ((S - 1008), 64)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
      - apply (Hx (A, 144)). right; left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR3.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. eapply L5PK.wr_fresh. exact FRSH_A. lia. lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  clear AG3 FR3 MS3. try clear STAT3. try clear K2.
  try clear c2_Sm840. try clear c2_Sm848. try clear c2_Sm856. try clear c2_Sm864. try clear c2_Sm872. try clear c2_Sm776. try clear c2_Sm784. try clear c2_Sm792. try clear c2_Sm800. try clear c2_Sm472. try clear c2_Sm480. try clear c2_Sm488. try clear c2_Sm496. try clear c2_Sm504. try clear c2_Sm512. try clear c2_Sm520. try clear c2_Sm528. try clear c2_Sm536. try clear c2_Sm544. try clear c2_Sm552. try clear c2_Sm560. try clear c2_Sm568. try clear c2_Sm424. try clear c2_Sm432. try clear c2_Sm360. try clear c2_Sm368. try clear c2_Sm376. try clear c2_Sm56. try clear c2_Sm64. try clear c2_Sm72. try clear c2_Sm80. try clear c2_Sm88. try clear c2_Sm96. try clear c2_Sm104. try clear c2_Sm112. try clear c2_Sm120. try clear c2_Sm128. try clear c2_Sm136. try clear c2_Sm144. try clear c2_Sm152. try clear c2_Sm8. try clear c2_Sm16. try clear c2_Sm696w1. try clear c2_Sm664w1. try clear c2_Sm640. try clear c2_Sm648. try clear c2_Sm632w1. try clear c2_Sm608. try clear c2_Sm616. try clear c2_Sm600w1. try clear c2_Sm464w1. try clear c2_Sm408w1. try clear c2_Sm280w1. try clear c2_Sm248w1. try clear c2_Sm216w1. try clear c2_Sm192. try clear c2_Sm200. try clear c2_Sm184w1. try clear c2_Sm160. try clear c2_Sm168. try clear c2_Sm48w1. try clear c2_Sm944. try clear c2_Sm936. try clear c2_Sm920. try clear c2_Sm912. try clear c2_Sm904. try clear R2_2. try clear R2_3. try clear R2_4. try clear R2_8. try clear R2_9. try clear R2_20. try clear R2_10. try clear DEF2. try clear HH2. try clear HQ2. try clear ES2. try clear DEFA_2. try clear DEFd1_2. try clear DEFd2_2. try clear DEFd3_2. try clear DEFd4_2.
  assert (c3_Om128z8: forall i, 0 <= i < 8 -> L5.u8_at RSEGS M3 (A + i) 0). { clear - ZA3. intros i Hi. replace (A + i) with ((A + 128 - 128) + i) by lia. apply (u8_of_zeros M3 (A + 128 - 128) 144 i ZA3). lia. }
  assert (c3_Om80z12: forall i, 0 <= i < 12 -> L5.u8_at RSEGS M3 ((A + 48) + i) 0). { clear - ZA3. intros i Hi. replace ((A + 48) + i) with ((A + 128 - 128) + (48 + i)) by lia. apply (u8_of_zeros M3 (A + 128 - 128) 144 (48 + i) ZA3). lia. }
  clear ZA3.
  (* [comment removed for export] *)
  pose proof ES3 as (S_1 & S_2 & S_3 & S_4 & S_5 & S_6 & S_7 & S_8 & S_9 & S_10 & S_11 & S_12 & S_13 & S_14 & S_15 & S_16 & S_17 & S_18 & S_19 & S_20).
  unfold EH_CAUGHT, EH_UNCAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, GLOBAL_LOCALE, CANARY, AUXVP in S_1, S_2, S_3, S_4, S_5, S_6, S_7, S_8, S_9.
  pose proof (auxv_cells M3 av uid rnd hw S_13) as (X_0 & X_1 & X_2 & X_3 & X_4 & X_5 & X_6 & X_7 & X_8 & X_9 & X_10 & X_11 & X_12 & X_13 & X_14 & X_15 & X_16 & X_17 & X_18 & X_19).
  assert (WUW: L5.writable RSEGS M3 459617 6). { apply (writable_img M3 UW_FLAGS 6 wseg_uwflags); unfold UW_FLAGS; kl. }
  assert (WUC: L5.writable RSEGS M3 456960 4). { apply (writable_img M3 EH_UNCAUGHT 4 wseg_uncaught); unfold EH_UNCAUGHT; kl. }
  unshelve epose proof (e3s1_conc fx3 R3 M3 (S - 896) (A + 128) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    as (fx4 & R4 & M4 & MS4 & K4 & R4_1 & R4_2 & R4_8 & R4_9 & R4_10 & R4_11 & R4_18 & R4_20 & C4_0 & C4_1 & C4_2 & C4_3 & C4_4 & C4_5 & C4_6 & C4_7 & FR4 & GR4).
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEF3 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEF3); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEF3 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (L5.defined_sub _ _ _ _ _ DEF3); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) clear - DEFA_3 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS _ _ _ DEFA_3); lia | lia | lia]. }
  { (* [comment removed for export] *) clear - DEFA_3 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. apply (L5.defined_sub _ _ _ _ _ DEFA_3); lia. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  { (* [comment removed for export] *) pr. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS4.
  (* [comment removed for export] *)
  assert (AG4: forall a k, ((a + k <= (S - 1024) \/ (S - 896) <= a) /\ 0 <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M3 M4 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
  { intros a k (E0 & Ha & Hk). split; [| split; [exact Ha | exact Hk]]. intros i Hi. apply FR4; [rewrite BG.unsigned_lit by (clear - Ha Hk Hi; lia); clear - E0 Hi; lia]. }
  assert (R4_1n: getr R4 (reg 1) = Z_to_bv 64 368844) by (rewrite R4_1; f_equal; ring). clear R4_1. rename R4_1n into R4_1.
  assert (R4_2n: getr R4 (reg 2) = Z_to_bv 64 (S - 960)) by (rewrite R4_2; f_equal; ring). clear R4_2. rename R4_2n into R4_2.
  assert (R4_3: getr R4 (reg 3) = Z_to_bv 64 67584) by (kin K4 3%nat; exact R3_3).
  assert (R4_4: getr R4 (reg 4) = Z_to_bv 64 459832) by (kin K4 4%nat; exact R3_4).
  assert (R4_8n: getr R4 (reg 8) = Z_to_bv 64 48) by (rewrite R4_8; f_equal; ring). clear R4_8. rename R4_8n into R4_8.
  assert (R4_9n: getr R4 (reg 9) = Z_to_bv 64 41) by (rewrite R4_9; f_equal; ring). clear R4_9. rename R4_9n into R4_9.
  assert (R4_10n: getr R4 (reg 10) = Z_to_bv 64 48) by (rewrite R4_10; f_equal; ring). clear R4_10. rename R4_10n into R4_10.
  assert (R4_11n: getr R4 (reg 11) = Z_to_bv 64 18446744073709551608) by (rewrite R4_11; f_equal; ring). clear R4_11. rename R4_11n into R4_11.
  assert (R4_18n: getr R4 (reg 18) = Z_to_bv 64 (S - 896)) by (rewrite R4_18; f_equal; ring). clear R4_18. rename R4_18n into R4_18.
  assert (R4_20n: getr R4 (reg 20) = Z_to_bv 64 48) by (rewrite R4_20; f_equal; ring). clear R4_20. rename R4_20n into R4_20.
  assert (c4_Sm840: L5.u64_at RSEGS M4 (S - 840) 135392) by (clear - AG4 c3_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm840]).
  assert (c4_Sm848: L5.u64_at RSEGS M4 (S - 848) (S + 64)) by (clear - AG4 c3_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm848]).
  assert (c4_Sm856: L5.u64_at RSEGS M4 (S - 856) w856) by (clear - AG4 c3_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm856]).
  assert (c4_Sm864: L5.u64_at RSEGS M4 (S - 864) w864) by (clear - AG4 c3_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm864]).
  assert (c4_Sm872: L5.u64_at RSEGS M4 (S - 872) w872) by (clear - AG4 c3_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm872]).
  assert (c4_Sm776: L5.u64_at RSEGS M4 (S - 776) 139520) by (clear - AG4 c3_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm776]).
  assert (c4_Sm784: L5.u64_at RSEGS M4 (S - 784) w784) by (clear - AG4 c3_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm784]).
  assert (c4_Sm792: L5.u64_at RSEGS M4 (S - 792) (S + 64)) by (clear - AG4 c3_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm792]).
  assert (c4_Sm800: L5.u64_at RSEGS M4 (S - 800) (S + 64)) by (clear - AG4 c3_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm800]).
  assert (c4_Sm472: L5.u64_at RSEGS M4 (S - 472) 142136) by (clear - AG4 c3_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm472]).
  assert (c4_Sm480: L5.u64_at RSEGS M4 (S - 480) (S + 64)) by (clear - AG4 c3_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm480]).
  assert (c4_Sm488: L5.u64_at RSEGS M4 (S - 488) w488) by (clear - AG4 c3_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm488]).
  assert (c4_Sm496: L5.u64_at RSEGS M4 (S - 496) (S + 64)) by (clear - AG4 c3_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm496]).
  assert (c4_Sm504: L5.u64_at RSEGS M4 (S - 504) w504) by (clear - AG4 c3_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm504]).
  assert (c4_Sm512: L5.u64_at RSEGS M4 (S - 512) w512) by (clear - AG4 c3_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm512]).
  assert (c4_Sm520: L5.u64_at RSEGS M4 (S - 520) w520) by (clear - AG4 c3_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm520]).
  assert (c4_Sm528: L5.u64_at RSEGS M4 (S - 528) w528) by (clear - AG4 c3_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm528]).
  assert (c4_Sm536: L5.u64_at RSEGS M4 (S - 536) w536) by (clear - AG4 c3_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm536]).
  assert (c4_Sm544: L5.u64_at RSEGS M4 (S - 544) w544) by (clear - AG4 c3_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm544]).
  assert (c4_Sm552: L5.u64_at RSEGS M4 (S - 552) w552) by (clear - AG4 c3_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm552]).
  assert (c4_Sm560: L5.u64_at RSEGS M4 (S - 560) w560) by (clear - AG4 c3_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm560]).
  assert (c4_Sm568: L5.u64_at RSEGS M4 (S - 568) w568) by (clear - AG4 c3_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm568]).
  assert (c4_Sm424: L5.u64_at RSEGS M4 (S - 424) 141264) by (clear - AG4 c3_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm424]).
  assert (c4_Sm432: L5.u64_at RSEGS M4 (S - 432) (S + 64)) by (clear - AG4 c3_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm432]).
  assert (c4_Sm360: L5.u64_at RSEGS M4 (S - 360) 139904) by (clear - AG4 c3_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm360]).
  assert (c4_Sm368: L5.u64_at RSEGS M4 (S - 368) (S + 64)) by (clear - AG4 c3_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm368]).
  assert (c4_Sm376: L5.u64_at RSEGS M4 (S - 376) (S - 48)) by (clear - AG4 c3_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm376]).
  assert (c4_Sm56: L5.u64_at RSEGS M4 (S - 56) 138528) by (clear - AG4 c3_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm56]).
  assert (c4_Sm64: L5.u64_at RSEGS M4 (S - 64) (S + 64)) by (clear - AG4 c3_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm64]).
  assert (c4_Sm72: L5.u64_at RSEGS M4 (S - 72) (U R0 9)) by (clear - AG4 c3_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm72]).
  assert (c4_Sm80: L5.u64_at RSEGS M4 (S - 80) (U R0 18)) by (clear - AG4 c3_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm80]).
  assert (c4_Sm88: L5.u64_at RSEGS M4 (S - 88) (U R0 19)) by (clear - AG4 c3_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm88]).
  assert (c4_Sm96: L5.u64_at RSEGS M4 (S - 96) (U R0 20)) by (clear - AG4 c3_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm96]).
  assert (c4_Sm104: L5.u64_at RSEGS M4 (S - 104) (U R0 21)) by (clear - AG4 c3_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm104]).
  assert (c4_Sm112: L5.u64_at RSEGS M4 (S - 112) (U R0 22)) by (clear - AG4 c3_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm112]).
  assert (c4_Sm120: L5.u64_at RSEGS M4 (S - 120) (U R0 23)) by (clear - AG4 c3_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm120]).
  assert (c4_Sm128: L5.u64_at RSEGS M4 (S - 128) (U R0 24)) by (clear - AG4 c3_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm128]).
  assert (c4_Sm136: L5.u64_at RSEGS M4 (S - 136) (U R0 25)) by (clear - AG4 c3_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm136]).
  assert (c4_Sm144: L5.u64_at RSEGS M4 (S - 144) (U R0 26)) by (clear - AG4 c3_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm144]).
  assert (c4_Sm152: L5.u64_at RSEGS M4 (S - 152) (U R0 27)) by (clear - AG4 c3_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm152]).
  assert (c4_Sm8: L5.u64_at RSEGS M4 (S - 8) 132608) by (clear - AG4 c3_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm8]).
  assert (c4_Sm16: L5.u64_at RSEGS M4 (S - 16) (U R0 8)) by (clear - AG4 c3_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm16]).
  assert (c4_Sm696w1: L5.u8_at RSEGS M4 (S - 696) fb696) by (clear - AG4 c3_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm696w1]).
  assert (c4_Sm664w1: L5.u8_at RSEGS M4 (S - 664) fb664) by (clear - AG4 c3_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm664w1]).
  assert (c4_Sm640: L5.u64_at RSEGS M4 (S - 640) d1) by (clear - AG4 c3_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm640]).
  assert (c4_Sm648: L5.u64_at RSEGS M4 (S - 648) 8) by (clear - AG4 c3_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm648]).
  assert (c4_Sm632w1: L5.u8_at RSEGS M4 (S - 632) fb632) by (clear - AG4 c3_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm632w1]).
  assert (c4_Sm608: L5.u64_at RSEGS M4 (S - 608) d2) by (clear - AG4 c3_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm608]).
  assert (c4_Sm616: L5.u64_at RSEGS M4 (S - 616) 8) by (clear - AG4 c3_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm616]).
  assert (c4_Sm600w1: L5.u8_at RSEGS M4 (S - 600) fb600) by (clear - AG4 c3_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm600w1]).
  assert (c4_Sm464w1: L5.u8_at RSEGS M4 (S - 464) fb464) by (clear - AG4 c3_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm464w1]).
  assert (c4_Sm408w1: L5.u8_at RSEGS M4 (S - 408) fb408) by (clear - AG4 c3_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm408w1]).
  assert (c4_Sm280w1: L5.u8_at RSEGS M4 (S - 280) fb280) by (clear - AG4 c3_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm280w1]).
  assert (c4_Sm248w1: L5.u8_at RSEGS M4 (S - 248) fb248) by (clear - AG4 c3_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm248w1]).
  assert (c4_Sm216w1: L5.u8_at RSEGS M4 (S - 216) fb216) by (clear - AG4 c3_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm216w1]).
  assert (c4_Sm192: L5.u64_at RSEGS M4 (S - 192) d3) by (clear - AG4 c3_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm192]).
  assert (c4_Sm200: L5.u64_at RSEGS M4 (S - 200) 8) by (clear - AG4 c3_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm200]).
  assert (c4_Sm184w1: L5.u8_at RSEGS M4 (S - 184) fb184) by (clear - AG4 c3_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm184w1]).
  assert (c4_Sm160: L5.u64_at RSEGS M4 (S - 160) d4) by (clear - AG4 c3_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm160]).
  assert (c4_Sm168: L5.u64_at RSEGS M4 (S - 168) 8) by (clear - AG4 c3_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M3 M4 _ _ _ (AG4 _ 8)); [lia | exact c3_Sm168]).
  assert (c4_Sm48w1: L5.u8_at RSEGS M4 (S - 48) fb48) by (clear - AG4 c3_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | exact c3_Sm48w1]).
  assert (c4_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M4 (A + i) 0)) by (clear - AG4 c3_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | apply c3_Om128z8; exact Hi]).
  assert (c4_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M4 ((A + 48) + i) 0)) by (clear - AG4 c3_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (tr8 M3 M4 _ _ _ (AG4 _ 1)); [lia | apply c3_Om80z12; exact Hi]).
  assert (c4_Sm960: L5.u64_at RSEGS M4 (S - 960) 74669) by (cellfix C4_0). clear C4_0.
  assert (c4_Sm952: L5.u64_at RSEGS M4 (S - 952) 136012) by (cellfix C4_1). clear C4_1.
  rewrite R3_20, BG.unsigned_lit in C4_2 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI).
  assert (c4_Sm944: L5.u64_at RSEGS M4 (S - 944) (S - 584)) by (cellfix C4_2). clear C4_2.
  set (u3_19 := U R3 19). assert (Wu3_19: 0 <= u3_19 < 2 ^ 64) by (unfold u3_19, U; apply wrange).
  assert (R3_19: getr R3 (reg 19) = Z_to_bv 64 u3_19) by (unfold u3_19, U; symmetry; apply lit_of_word). clearbody u3_19.
  rewrite R3_19, BG.unsigned_lit in C4_3 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_19).
  assert (c4_Sm936: L5.u64_at RSEGS M4 (S - 936) u3_19) by (cellfix C4_3). clear C4_3.
  set (u3_18 := U R3 18). assert (Wu3_18: 0 <= u3_18 < 2 ^ 64) by (unfold u3_18, U; apply wrange).
  assert (R3_18: getr R3 (reg 18) = Z_to_bv 64 u3_18) by (unfold u3_18, U; symmetry; apply lit_of_word). clearbody u3_18.
  rewrite R3_18, BG.unsigned_lit in C4_4 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu3_18).
  assert (c4_Sm928: L5.u64_at RSEGS M4 (S - 928) u3_18) by (cellfix C4_4). clear C4_4.
  rewrite R3_9, BG.unsigned_lit in C4_5 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI Wu0_9).
  assert (c4_Sm920: L5.u64_at RSEGS M4 (S - 920) u0_9) by (cellfix C4_5). clear C4_5.
  rewrite R3_8, BG.unsigned_lit in C4_6 by (kl LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A).
  assert (c4_Sm912: L5.u64_at RSEGS M4 (S - 912) (A + 128)) by (cellfix C4_6). clear C4_6.
  assert (c4_Sm904: L5.u64_at RSEGS M4 (S - 904) 136328) by (cellfix C4_7). clear C4_7.
  assert (STAT4: forall a, stat_rd av a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { clear - FR4 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. intros a Ha. unfold stat_rd, EH_CAUGHT, SYSCAT_GUARD, UW_FLAGS, TD_LOCALE, LOCALE_MSGCAT, CANARY, AUXVP in Ha. apply FR4; rewrite BG.unsigned_lit by lia; lia. }
  pose proof (e1_statics_keep M3 M4 gd fl av uid rnd canary hw ES3 STAT4) as ES4.
  assert (DEF4: L5.defined M4 (S - 10240) 10240) by (eapply L5.defined_grows; [exact GR4 | exact DEF3]).
  assert (DEFA_4: L5.defined M4 A 144) by (eapply L5.defined_grows; [exact GR4 | exact DEFA_3]).
  assert (DEFd1_4: L5.defined M4 d1 64) by (eapply L5.defined_grows; [exact GR4 | exact DEFd1_3]).
  assert (DEFd2_4: L5.defined M4 d2 64) by (eapply L5.defined_grows; [exact GR4 | exact DEFd2_3]).
  assert (DEFd3_4: L5.defined M4 d3 64) by (eapply L5.defined_grows; [exact GR4 | exact DEFd3_3]).
  assert (DEFd4_4: L5.defined M4 d4 64) by (eapply L5.defined_grows; [exact GR4 | exact DEFd4_3]).
  assert (HH4: hi_heap HI ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (cr) 144) M4 (m_vmmaps model2)).
  { clear - HH3 GR4 FR4 hi_heap_clientx LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply hi_heap_clientx. exact HH3. lia. 2: exact GR4. intros a Ha.
    destruct (in_dec (S - 1024) (S - 896) a) as [IN0|OUT0]. { right; left; lia. }
    left; apply FR4; rewrite BG.unsigned_lit by lia; lia. }
  assert (HQ4: L5C.hpres L LB1 S 10240 XSF M M4).
  { clear - LBWF HQ3 FR4 GR4 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. eapply (L5PK.hpres_step_pure L IMGHI STOP ERR LB1 S 10240 XSF M M3 M4 [((S - 1024), 128)]). exact LBWF. lia. exact HQ3.
    { intros x Hx. apply FR4; intros Hin.
        apply (Hx ((S - 1024), 128)). left; reflexivity. unfold L5.in_rng; cbn. clear - Hin; lia.
    }
    exact GR4.
    constructor. apply L5PK.wr_scratch; lia.
    constructor. }
  clear X_0 X_1 X_2 X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11 X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19 S_1 S_2 S_3 S_4 S_5 S_6 S_7 S_8 S_9 S_10 S_11 S_12 S_13 S_14 S_15 S_16 S_17 S_18 S_19 S_20. try clear WUW WUC. try clear U_0 U_1 U_2 U_3 U_4 U_5.
  assert (R4_19: getr R4 (reg 19) = Z_to_bv 64 u3_19) by (kin K4 19%nat; exact R3_19).
  clear AG4 FR4 MS4. try clear STAT4. try clear K3.
  try clear c3_Sm840. try clear c3_Sm848. try clear c3_Sm856. try clear c3_Sm864. try clear c3_Sm872. try clear c3_Sm776. try clear c3_Sm784. try clear c3_Sm792. try clear c3_Sm800. try clear c3_Sm472. try clear c3_Sm480. try clear c3_Sm488. try clear c3_Sm496. try clear c3_Sm504. try clear c3_Sm512. try clear c3_Sm520. try clear c3_Sm528. try clear c3_Sm536. try clear c3_Sm544. try clear c3_Sm552. try clear c3_Sm560. try clear c3_Sm568. try clear c3_Sm424. try clear c3_Sm432. try clear c3_Sm360. try clear c3_Sm368. try clear c3_Sm376. try clear c3_Sm56. try clear c3_Sm64. try clear c3_Sm72. try clear c3_Sm80. try clear c3_Sm88. try clear c3_Sm96. try clear c3_Sm104. try clear c3_Sm112. try clear c3_Sm120. try clear c3_Sm128. try clear c3_Sm136. try clear c3_Sm144. try clear c3_Sm152. try clear c3_Sm8. try clear c3_Sm16. try clear c3_Sm696w1. try clear c3_Sm664w1. try clear c3_Sm640. try clear c3_Sm648. try clear c3_Sm632w1. try clear c3_Sm608. try clear c3_Sm616. try clear c3_Sm600w1. try clear c3_Sm464w1. try clear c3_Sm408w1. try clear c3_Sm280w1. try clear c3_Sm248w1. try clear c3_Sm216w1. try clear c3_Sm192. try clear c3_Sm200. try clear c3_Sm184w1. try clear c3_Sm160. try clear c3_Sm168. try clear c3_Sm48w1. try clear c3_Sm944. try clear c3_Sm936. try clear c3_Sm920. try clear c3_Sm912. try clear c3_Sm904. try clear c3_Om128z8. try clear c3_Om80z12. try clear R3_1. try clear R3_2. try clear R3_3. try clear R3_4. try clear R3_8. try clear R3_9. try clear R3_10. try clear R3_11. try clear R3_20. try clear R3_19. try clear R3_18. try clear DEF3. try clear HH3. try clear HQ3. try clear ES3. try clear DEFA_3. try clear DEFd1_3. try clear DEFd2_3. try clear DEFd3_3. try clear DEFd4_3.
  (* [comment removed for export] *)
  pose proof (hio_malloc L SCFG HI HIok fx4 R4 M4 model2 ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (debit L (cr) 144) 48 K) as HC.
  rewrite (ly_segs L LY), (ly_malloc L LY), (ly_tp L LY) in HC. apply HC; clear HC.
  - exact HH4.
  - exact Mh.
  - exact Ml.
  - exact Mm.
  - rewrite L5CoreKit.L5K.rl10. exact R4_10.
  - kl.
  - exact CR48.
  - rewrite L5CoreKit.L5K.rl4. exact R4_4.
  - rewrite L5CoreKit.L5K.rl1, R4_1. apply L5CoreKit.L5K.ret_ok_lit. apply ra_ok_lit. kl. reflexivity.
  - clear - R4_2 A16 DEF4 LY SLO SHI STOP. unfold stack_ok, hl_ceil. rewrite (ly_stack L LY), (ly_segs L LY). rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit by lia.
    split. { match goal with |- ?x mod 16 = 0 => replace x with (S + (-60) * 16) by lia end. rewrite Z_mod_plus_full. exact A16. }
    unfold HEAP_STACK. split. lia. split. lia. split. lia.
    intros d m0 Hd Hm. assert (WW: L5.writable RSEGS M4 (S - 10240) 10240). { apply (L5C.writable_of_defined RSEGS). exact DEF4. lia. lia. }
    match goal with |- store_ok _ _ (Z_to_bv 64 ?a) _ = true => replace a with (S - 10240 + (a - (S - 10240))) by ring end. apply WW; lia.
  - exact HK0.
  - intros R5 M5 model5 msg HA10 RP5 BRn BAn DEFn PRES5 MBVn HH5.
    rewrite L5CoreKit.L5K.rl1, R4_1.
    rewrite L5CoreKit.L5K.rl2, R4_2, BG.unsigned_lit in PRES5 by (kl SLO SHI STOP).
    match type of PRES5 with heap_pres_core _ _ ?x _ _ => replace x with (S - 960) in PRES5 by (kl SLO SHI STOP) end.
    pose proof (hpres_of_core L ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 960) M4 M5 PRES5) as HP5. rewrite (ly_stack L LY) in HP5. unfold HEAP_STACK in HP5.
    assert (AGS5: forall a k, ((S - 960) <= a /\ a + k <= 2 ^ 64) -> L5C.agree_on M4 M5 a k /\ 0 <= a /\ a + k <= 2 ^ 64).
    { clear - HP5 IMGHI STOP ERR LY SLO SHI. intros a k [Ha Hk]. split; [| split; [lia | exact Hk]]. eapply (L5PK.agree_call_stack L IMGHI STOP ERR). exact HP5. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB5_A: L5C.agree_on M4 M5 A 144).
    { clear - HP5 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP5. left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_A. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB5_d1: L5C.agree_on M4 M5 d1 64).
    { clear - HP5 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d1 B1_d1 B3_d1 B4_d1. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP5. right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d1. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB5_d2: L5C.agree_on M4 M5 d2 64).
    { clear - HP5 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d2 B1_d2 B3_d2 B4_d2. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP5. right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d2. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB5_d3: L5C.agree_on M4 M5 d3 64).
    { clear - HP5 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d3 B1_d3 B3_d3 B4_d3. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP5. right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d3. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (AGB5_d4: L5C.agree_on M4 M5 d4 64).
    { clear - HP5 IMGHI STOP ERR LY LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_d4 B1_d4 B3_d4 B4_d4. eapply (L5PK.agree_call_block L IMGHI STOP ERR). exact HP5. right; right; right; right; left; reflexivity. lia. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_d4. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    assert (STAT5: forall a, stat_rd av a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
    { clear - HP5 stat_keep_hpres LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI. apply (stat_keep_hpres av ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 960) 8224 [] M4 M5 HP5). lia. lia. lia. lia. lia. intros i Hi. apply L5C.outside_nil. }
    pose proof (e1_statics_keep M4 M5 gd fl av uid rnd canary hw ES4 STAT5) as ES5.
    assert (DEF5: L5.defined M5 (S - 10240) 10240).
    { clear - HP5 DEF4 defined_across IMGHI STOP ERR LY SLO SHI. eapply (defined_across ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) (S - 960) 8224 [] M4 M5). exact HP5. lia. lia. lia. lia. exact DEF4. }
    assert (DEFA_5: L5.defined M5 A 144) by (eapply (L5C.defined_agree M4 M5); [exact AGB5_A | exact DEFA_4]).
    assert (DEFd1_5: L5.defined M5 d1 64) by (eapply (L5C.defined_agree M4 M5); [exact AGB5_d1 | exact DEFd1_4]).
    assert (DEFd2_5: L5.defined M5 d2 64) by (eapply (L5C.defined_agree M4 M5); [exact AGB5_d2 | exact DEFd2_4]).
    assert (DEFd3_5: L5.defined M5 d3 64) by (eapply (L5C.defined_agree M4 M5); [exact AGB5_d3 | exact DEFd3_4]).
    assert (DEFd4_5: L5.defined M5 d4 64) by (eapply (L5C.defined_agree M4 M5); [exact AGB5_d4 | exact DEFd4_4]).
    assert (DEFmsg_5: L5.defined M5 msg 48) by exact DEFn. clear DEFn.
    pose proof BRn as BR_msg. clear BRn. pose proof BR_msg as (B0_msg & B1_msg & B2_msg & B3_msg & B4_msg). rewrite (ly_img_lo L LY), (ly_img_hi L LY) in B1_msg. unfold hl_ceil in B4_msg.
    pose proof (BAn (A, 144) ltac:(left; reflexivity)) as AP_msg_A. cbn [fst snd] in AP_msg_A.
    pose proof (BAn (d1, 64) ltac:(right; left; reflexivity)) as AP_msg_d1. cbn [fst snd] in AP_msg_d1.
    pose proof (BAn (d2, 64) ltac:(right; right; left; reflexivity)) as AP_msg_d2. cbn [fst snd] in AP_msg_d2.
    pose proof (BAn (d3, 64) ltac:(right; right; right; left; reflexivity)) as AP_msg_d3. cbn [fst snd] in AP_msg_d3.
    pose proof (BAn (d4, 64) ltac:(right; right; right; right; left; reflexivity)) as AP_msg_d4. cbn [fst snd] in AP_msg_d4.
    assert (FRSH_msg: L5PK.fresh_rng L LB1 msg 48). { clear - BAn LY B0_msg B1_msg B3_msg B4_msg STOP. split. lia. split. rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact B1_msg. split. lia. intros bb Hbb. apply BAn. right. right. right. right. right.  exact Hbb. }
    clear BAn.
    assert (MOK5: model_ok model5).
    { destruct MOK2 as (Y1 & Y2 & Y3); split; [rewrite (L5C.halted_but_vm _ _ MBVn); exact Y1 | split; [rewrite (L5C.lazy_but_vm _ _ MBVn); exact Y2 | rewrite (L5C.materialized_but_vm _ _ MBVn); exact Y3]]. }
    clear Mh Ml Mm. pose proof MOK5 as (Mh & Ml & Mm).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV2 MBVn) as MBV5. clear MBVn MBV2.
    assert (RPi5: forall i, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr R4 (reg i)).
    { intros i Hi. apply (L5CoreKit.L5K.regs_preserved_index R4 R5 i RP5). exact Hi. }
    assert (R5_2: getr R5 (reg 2) = Z_to_bv 64 (S - 960)) by (rewrite (RPi5 2%nat) by inl; exact R4_2).
    assert (R5_3: getr R5 (reg 3) = Z_to_bv 64 67584) by (rewrite (RPi5 3%nat) by inl; exact R4_3).
    assert (R5_4: getr R5 (reg 4) = Z_to_bv 64 459832) by (rewrite (RPi5 4%nat) by inl; exact R4_4).
    assert (R5_8: getr R5 (reg 8) = Z_to_bv 64 48) by (rewrite (RPi5 8%nat) by inl; exact R4_8).
    assert (R5_9: getr R5 (reg 9) = Z_to_bv 64 41) by (rewrite (RPi5 9%nat) by inl; exact R4_9).
    assert (R5_18: getr R5 (reg 18) = Z_to_bv 64 (S - 896)) by (rewrite (RPi5 18%nat) by inl; exact R4_18).
    assert (R5_19: getr R5 (reg 19) = Z_to_bv 64 u3_19) by (rewrite (RPi5 19%nat) by inl; exact R4_19).
    assert (R5_20: getr R5 (reg 20) = Z_to_bv 64 48) by (rewrite (RPi5 20%nat) by inl; exact R4_20).
    rewrite L5CoreKit.L5K.rl10 in HA10. rename HA10 into R5_10.
    assert (c5_Sm840: L5.u64_at RSEGS M5 (S - 840) 135392) by (clear - AGS5 c4_Sm840 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm840]).
    assert (c5_Sm848: L5.u64_at RSEGS M5 (S - 848) (S + 64)) by (clear - AGS5 c4_Sm848 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm848]).
    assert (c5_Sm856: L5.u64_at RSEGS M5 (S - 856) w856) by (clear - AGS5 c4_Sm856 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm856]).
    assert (c5_Sm864: L5.u64_at RSEGS M5 (S - 864) w864) by (clear - AGS5 c4_Sm864 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm864]).
    assert (c5_Sm872: L5.u64_at RSEGS M5 (S - 872) w872) by (clear - AGS5 c4_Sm872 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm872]).
    assert (c5_Sm776: L5.u64_at RSEGS M5 (S - 776) 139520) by (clear - AGS5 c4_Sm776 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm776]).
    assert (c5_Sm784: L5.u64_at RSEGS M5 (S - 784) w784) by (clear - AGS5 c4_Sm784 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm784]).
    assert (c5_Sm792: L5.u64_at RSEGS M5 (S - 792) (S + 64)) by (clear - AGS5 c4_Sm792 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm792]).
    assert (c5_Sm800: L5.u64_at RSEGS M5 (S - 800) (S + 64)) by (clear - AGS5 c4_Sm800 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm800]).
    assert (c5_Sm472: L5.u64_at RSEGS M5 (S - 472) 142136) by (clear - AGS5 c4_Sm472 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm472]).
    assert (c5_Sm480: L5.u64_at RSEGS M5 (S - 480) (S + 64)) by (clear - AGS5 c4_Sm480 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm480]).
    assert (c5_Sm488: L5.u64_at RSEGS M5 (S - 488) w488) by (clear - AGS5 c4_Sm488 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm488]).
    assert (c5_Sm496: L5.u64_at RSEGS M5 (S - 496) (S + 64)) by (clear - AGS5 c4_Sm496 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm496]).
    assert (c5_Sm504: L5.u64_at RSEGS M5 (S - 504) w504) by (clear - AGS5 c4_Sm504 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm504]).
    assert (c5_Sm512: L5.u64_at RSEGS M5 (S - 512) w512) by (clear - AGS5 c4_Sm512 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm512]).
    assert (c5_Sm520: L5.u64_at RSEGS M5 (S - 520) w520) by (clear - AGS5 c4_Sm520 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm520]).
    assert (c5_Sm528: L5.u64_at RSEGS M5 (S - 528) w528) by (clear - AGS5 c4_Sm528 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm528]).
    assert (c5_Sm536: L5.u64_at RSEGS M5 (S - 536) w536) by (clear - AGS5 c4_Sm536 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm536]).
    assert (c5_Sm544: L5.u64_at RSEGS M5 (S - 544) w544) by (clear - AGS5 c4_Sm544 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm544]).
    assert (c5_Sm552: L5.u64_at RSEGS M5 (S - 552) w552) by (clear - AGS5 c4_Sm552 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm552]).
    assert (c5_Sm560: L5.u64_at RSEGS M5 (S - 560) w560) by (clear - AGS5 c4_Sm560 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm560]).
    assert (c5_Sm568: L5.u64_at RSEGS M5 (S - 568) w568) by (clear - AGS5 c4_Sm568 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm568]).
    assert (c5_Sm424: L5.u64_at RSEGS M5 (S - 424) 141264) by (clear - AGS5 c4_Sm424 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm424]).
    assert (c5_Sm432: L5.u64_at RSEGS M5 (S - 432) (S + 64)) by (clear - AGS5 c4_Sm432 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm432]).
    assert (c5_Sm360: L5.u64_at RSEGS M5 (S - 360) 139904) by (clear - AGS5 c4_Sm360 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm360]).
    assert (c5_Sm368: L5.u64_at RSEGS M5 (S - 368) (S + 64)) by (clear - AGS5 c4_Sm368 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm368]).
    assert (c5_Sm376: L5.u64_at RSEGS M5 (S - 376) (S - 48)) by (clear - AGS5 c4_Sm376 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm376]).
    assert (c5_Sm56: L5.u64_at RSEGS M5 (S - 56) 138528) by (clear - AGS5 c4_Sm56 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm56]).
    assert (c5_Sm64: L5.u64_at RSEGS M5 (S - 64) (S + 64)) by (clear - AGS5 c4_Sm64 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm64]).
    assert (c5_Sm72: L5.u64_at RSEGS M5 (S - 72) (U R0 9)) by (clear - AGS5 c4_Sm72 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm72]).
    assert (c5_Sm80: L5.u64_at RSEGS M5 (S - 80) (U R0 18)) by (clear - AGS5 c4_Sm80 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm80]).
    assert (c5_Sm88: L5.u64_at RSEGS M5 (S - 88) (U R0 19)) by (clear - AGS5 c4_Sm88 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm88]).
    assert (c5_Sm96: L5.u64_at RSEGS M5 (S - 96) (U R0 20)) by (clear - AGS5 c4_Sm96 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm96]).
    assert (c5_Sm104: L5.u64_at RSEGS M5 (S - 104) (U R0 21)) by (clear - AGS5 c4_Sm104 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm104]).
    assert (c5_Sm112: L5.u64_at RSEGS M5 (S - 112) (U R0 22)) by (clear - AGS5 c4_Sm112 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm112]).
    assert (c5_Sm120: L5.u64_at RSEGS M5 (S - 120) (U R0 23)) by (clear - AGS5 c4_Sm120 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm120]).
    assert (c5_Sm128: L5.u64_at RSEGS M5 (S - 128) (U R0 24)) by (clear - AGS5 c4_Sm128 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm128]).
    assert (c5_Sm136: L5.u64_at RSEGS M5 (S - 136) (U R0 25)) by (clear - AGS5 c4_Sm136 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm136]).
    assert (c5_Sm144: L5.u64_at RSEGS M5 (S - 144) (U R0 26)) by (clear - AGS5 c4_Sm144 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm144]).
    assert (c5_Sm152: L5.u64_at RSEGS M5 (S - 152) (U R0 27)) by (clear - AGS5 c4_Sm152 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm152]).
    assert (c5_Sm8: L5.u64_at RSEGS M5 (S - 8) 132608) by (clear - AGS5 c4_Sm8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm8]).
    assert (c5_Sm16: L5.u64_at RSEGS M5 (S - 16) (U R0 8)) by (clear - AGS5 c4_Sm16 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm16]).
    assert (c5_Sm696w1: L5.u8_at RSEGS M5 (S - 696) fb696) by (clear - AGS5 c4_Sm696w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm696w1]).
    assert (c5_Sm664w1: L5.u8_at RSEGS M5 (S - 664) fb664) by (clear - AGS5 c4_Sm664w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm664w1]).
    assert (c5_Sm640: L5.u64_at RSEGS M5 (S - 640) d1) by (clear - AGS5 c4_Sm640 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm640]).
    assert (c5_Sm648: L5.u64_at RSEGS M5 (S - 648) 8) by (clear - AGS5 c4_Sm648 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm648]).
    assert (c5_Sm632w1: L5.u8_at RSEGS M5 (S - 632) fb632) by (clear - AGS5 c4_Sm632w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm632w1]).
    assert (c5_Sm608: L5.u64_at RSEGS M5 (S - 608) d2) by (clear - AGS5 c4_Sm608 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm608]).
    assert (c5_Sm616: L5.u64_at RSEGS M5 (S - 616) 8) by (clear - AGS5 c4_Sm616 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm616]).
    assert (c5_Sm600w1: L5.u8_at RSEGS M5 (S - 600) fb600) by (clear - AGS5 c4_Sm600w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm600w1]).
    assert (c5_Sm464w1: L5.u8_at RSEGS M5 (S - 464) fb464) by (clear - AGS5 c4_Sm464w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm464w1]).
    assert (c5_Sm408w1: L5.u8_at RSEGS M5 (S - 408) fb408) by (clear - AGS5 c4_Sm408w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm408w1]).
    assert (c5_Sm280w1: L5.u8_at RSEGS M5 (S - 280) fb280) by (clear - AGS5 c4_Sm280w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm280w1]).
    assert (c5_Sm248w1: L5.u8_at RSEGS M5 (S - 248) fb248) by (clear - AGS5 c4_Sm248w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm248w1]).
    assert (c5_Sm216w1: L5.u8_at RSEGS M5 (S - 216) fb216) by (clear - AGS5 c4_Sm216w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm216w1]).
    assert (c5_Sm192: L5.u64_at RSEGS M5 (S - 192) d3) by (clear - AGS5 c4_Sm192 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm192]).
    assert (c5_Sm200: L5.u64_at RSEGS M5 (S - 200) 8) by (clear - AGS5 c4_Sm200 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm200]).
    assert (c5_Sm184w1: L5.u8_at RSEGS M5 (S - 184) fb184) by (clear - AGS5 c4_Sm184w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm184w1]).
    assert (c5_Sm160: L5.u64_at RSEGS M5 (S - 160) d4) by (clear - AGS5 c4_Sm160 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm160]).
    assert (c5_Sm168: L5.u64_at RSEGS M5 (S - 168) 8) by (clear - AGS5 c4_Sm168 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm168]).
    assert (c5_Sm48w1: L5.u8_at RSEGS M5 (S - 48) fb48) by (clear - AGS5 c4_Sm48w1 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr8 M4 M5 _ _ _ (AGS5 _ 1)); [lia | exact c4_Sm48w1]).
    assert (c5_Om128z8: (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M5 (A + i) 0)) by (clear - AGB5_A c4_Om128z8 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB5_A); [lia | apply c4_Om128z8; exact Hi]).
    assert (c5_Om80z12: (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M5 ((A + 48) + i) 0)) by (clear - AGB5_A c4_Om80z12 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI B0_A B1_A B3_A B4_A; intros i Hi; eapply (trb8 _ _ _ _ _ _ AGB5_A); [lia | apply c4_Om80z12; exact Hi]).
    assert (c5_Sm960: L5.u64_at RSEGS M5 (S - 960) 74669) by (clear - AGS5 c4_Sm960 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm960]).
    assert (c5_Sm952: L5.u64_at RSEGS M5 (S - 952) 136012) by (clear - AGS5 c4_Sm952 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm952]).
    assert (c5_Sm944: L5.u64_at RSEGS M5 (S - 944) (S - 584)) by (clear - AGS5 c4_Sm944 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm944]).
    assert (c5_Sm936: L5.u64_at RSEGS M5 (S - 936) u3_19) by (clear - AGS5 c4_Sm936 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm936]).
    assert (c5_Sm928: L5.u64_at RSEGS M5 (S - 928) u3_18) by (clear - AGS5 c4_Sm928 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm928]).
    assert (c5_Sm920: L5.u64_at RSEGS M5 (S - 920) u0_9) by (clear - AGS5 c4_Sm920 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm920]).
    assert (c5_Sm912: L5.u64_at RSEGS M5 (S - 912) (A + 128)) by (clear - AGS5 c4_Sm912 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm912]).
    assert (c5_Sm904: L5.u64_at RSEGS M5 (S - 904) 136328) by (clear - AGS5 c4_Sm904 LY LYX HIok SLO SHI STOP AVTOP AVLO AVHI; eapply (tr64 M4 M5 _ _ _ (AGS5 _ 8)); [lia | exact c4_Sm904]).
    assert (HQ5: L5C.hpres L LB1 S 10240 XSF M M5).
    { clear - LBWF HQ4 HP5 IMGHI STOP ERR LY SLO SHI. eapply (L5PK.hpres_step_call L IMGHI STOP ERR LB1 ((A, 144) :: (d1, 64) :: (d2, 64) :: (d3, 64) :: (d4, 64) :: LB1) S 10240 XSF (S - 960) 8224 [] M M4 M5). exact LBWF. lia. lia. exact HQ4. exact HP5. intros bb Hbb; right; right; right; right; right;  exact Hbb. lia. lia. lia. constructor. }
    clear AGS5 STAT5 PRES5 RP5 RPi5 HP5 AGB5_A AGB5_d1 AGB5_d2 AGB5_d3 AGB5_d4.
    try clear c4_Sm840 c4_Sm848 c4_Sm856 c4_Sm864 c4_Sm872 c4_Sm776 c4_Sm784 c4_Sm792 c4_Sm800 c4_Sm472 c4_Sm480 c4_Sm488 c4_Sm496 c4_Sm504 c4_Sm512 c4_Sm520 c4_Sm528 c4_Sm536 c4_Sm544 c4_Sm552 c4_Sm560 c4_Sm568 c4_Sm424 c4_Sm432 c4_Sm360 c4_Sm368 c4_Sm376 c4_Sm56 c4_Sm64 c4_Sm72 c4_Sm80 c4_Sm88 c4_Sm96 c4_Sm104 c4_Sm112 c4_Sm120 c4_Sm128 c4_Sm136 c4_Sm144 c4_Sm152 c4_Sm8 c4_Sm16 c4_Sm696w1 c4_Sm664w1 c4_Sm640 c4_Sm648 c4_Sm632w1 c4_Sm608 c4_Sm616 c4_Sm600w1 c4_Sm464w1 c4_Sm408w1 c4_Sm280w1 c4_Sm248w1 c4_Sm216w1 c4_Sm192 c4_Sm200 c4_Sm184w1 c4_Sm160 c4_Sm168 c4_Sm48w1 c4_Om128z8 c4_Om80z12 c4_Sm960 c4_Sm952 c4_Sm944 c4_Sm936 c4_Sm928 c4_Sm920 c4_Sm912 c4_Sm904 R4_1 R4_2 R4_3 R4_4 R4_8 R4_9 R4_10 R4_11 R4_18 R4_20 R4_19 DEF4 HH4 HQ4 ES4 K4 DEFA_4 DEFd1_4 DEFd2_4 DEFd3_4 DEFd4_4.
    eapply (seg3 fx4 R0 R R5 M M5 model model5 K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 A msg u0_9 u3_19 u3_18 HK0 H02 H03 H04 A16 SLO SHI STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 Ww856 Ww864 Ww872 Ww784 Ww488 Ww504 Ww512 Ww520 Ww528 Ww536 Ww544 Ww552 Ww560 Ww568 Wu0_9 Wu3_19 Wu3_18 R5_2 R5_3 R5_4 R5_8 R5_9 R5_10 R5_18 R5_19 R5_20 c5_Sm840 c5_Sm848 c5_Sm856 c5_Sm864 c5_Sm872 c5_Sm776 c5_Sm784 c5_Sm792 c5_Sm800 c5_Sm472 c5_Sm480 c5_Sm488 c5_Sm496 c5_Sm504 c5_Sm512 c5_Sm520 c5_Sm528 c5_Sm536 c5_Sm544 c5_Sm552 c5_Sm560 c5_Sm568 c5_Sm424 c5_Sm432 c5_Sm360 c5_Sm368 c5_Sm376 c5_Sm56 c5_Sm64 c5_Sm72 c5_Sm80 c5_Sm88 c5_Sm96 c5_Sm104 c5_Sm112 c5_Sm120 c5_Sm128 c5_Sm136 c5_Sm144 c5_Sm152 c5_Sm8 c5_Sm16 c5_Sm696w1 c5_Sm664w1 c5_Sm640 c5_Sm648 c5_Sm632w1 c5_Sm608 c5_Sm616 c5_Sm600w1 c5_Sm464w1 c5_Sm408w1 c5_Sm280w1 c5_Sm248w1 c5_Sm216w1 c5_Sm192 c5_Sm200 c5_Sm184w1 c5_Sm160 c5_Sm168 c5_Sm48w1 c5_Om128z8 c5_Om80z12 c5_Sm960 c5_Sm952 c5_Sm944 c5_Sm936 c5_Sm928 c5_Sm920 c5_Sm912 c5_Sm904 ES5 DEF5 DEFmsg_5 DEFA_5 DEFd1_5 DEFd2_5 DEFd3_5 DEFd4_5 BR_msg BR_A BR_d1 BR_d2 BR_d3 BR_d4 AP_msg_A AP_msg_d1 AP_msg_d2 AP_msg_d3 AP_msg_d4 AP_A_d1 AP_A_d2 AP_A_d3 AP_A_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 FRSH_msg FRSH_A HH5 MOK5 MBV5 HQ5 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3S2.
