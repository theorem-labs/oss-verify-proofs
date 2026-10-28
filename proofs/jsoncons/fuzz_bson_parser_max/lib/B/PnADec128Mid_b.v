(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare AxSymExec3 L5Defs L5Kn L5KnA L5Core L5CoreKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModelFacts
     PnDecFacts PnDecBv PnMemW PnSDec128Rnd2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128Defs_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnADec128Bv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128P2_b PnADec128Rnd_b PnADec128Rnd3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADMID.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S F first sigma E1 : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 256 + 256 <= F \/ F + 512 <= S - 256.
Hypothesis FFI : 65536 + 6840320 <= F \/ F + 512 <= 65536.
Hypothesis Ffirst : 4096 <= first <= 140737488355280.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FE1 : 0 <= E1 < 2 ^ 64.
Variable V : Z.
Hypothesis FV : 0 <= V < 2 ^ 113.
Abbreviation cell := (PNADD.cell F).
Abbreviation digs := (PNADD.digs F V).
Abbreviation zers := (PNADD.zers F).
Abbreviation HD := (PNADRN3.HD R0 S F V).
Abbreviation bvu_small := PNSDRN2.bvu_small.
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 50%nat => F | 59%nat => E1 | _ => 0 end.
Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
Local Ltac lem T L := pose proof L as T; L5SAR.feed T ltac:(assumption).
Local Ltac keep1 KSa := first [ assumption | (rewrite KSa by inl; assumption) ].
Local Ltac keep2 KSa KSb := first [ assumption | (rewrite KSa by inl; first [ assumption | (rewrite KSb by inl; assumption) ]) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma V_lt35 : V < 10 ^ 35.
Proof. clear -FV. assert (2 ^ 113 < 10 ^ 35) by (vm_compute; reflexivity). lia. Qed.
Lemma dg0 : PNDF.dg V 0 = 0.
Proof. unfold PNDF.dg. replace (35 - 0) with 35 by (clear; lia). rewrite Z.div_small; [reflexivity|]. pose proof V_lt35. clear -H FV; lia. Qed.
(* [comment removed for export] *)
Lemma sh_cell i : 0 <= i <= 35 -> exists j, (F + 32 + 4 * i) / 8 = F / 8 + j /\ 4 <= j <= 21.
Proof.
  intros Hi. exists ((32 + 4 * i) / 8).
  assert (F8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(clear; lia)) as E. rewrite FF32, Z.add_0_r in E. rewrite E. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia). apply Z.mod_mul. clear; lia. }
  pose proof (Z.div_mod F 8 ltac:(clear; lia)) as E8. rewrite F8, Z.add_0_r in E8.
  split.
  - replace (F + 32 + 4 * i) with (F / 8 * 8 + (32 + 4 * i)) by (clear -E8; lia). apply Z.div_add_l. clear; lia.
  - split; [apply Z.div_le_lower_bound; clear -Hi; lia| apply Z.lt_succ_r; apply Z.div_lt_upper_bound; clear -Hi; lia].
Qed.

Abbreviation e14 := (Z.land E1 16383).
Lemma e14_range : 0 <= e14 <= 16383.
Proof. rewrite PNDBV.land_ones14. pose proof (Z.mod_pos_bound E1 (2 ^ 14) ltac:(clear; lia)) as B. clear -B; lia. Qed.

Lemma scan_loop (FVp : 0 < V) (n : nat) : forall fx R M i,
  35 - i = Z.of_nat n -> 0 <= i <= 34 -> V < 10 ^ (35 - i) ->
  PNADD.RBO R0 S F first sigma R -> getr R (reg 17) = Z_to_bv 64 E1 -> getr R (reg 5) = Z_to_bv 64 16383 -> getr R (reg 11) = Z_to_bv 64 18446744073709551611 ->
  getr R (reg 10) = Z_to_bv 64 (F + 36 + 4 * i) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * i) -> getr R (reg 13) = Z_to_bv 64 (36 - i) ->
  digs M 0 -> L5.writable RSEGS M (S - 256) 256 -> L5KA.zeros_at M (PNADD.SH F + 4) 18 ->
  exists fx' R' z, msteps RSEGS (st fx R 0xb4564 M) (st fx' R' 0xb4294 M) /\ PNADD.stP R0 S F first sigma e14 z (36 - z) R' /\ i < z <= 35.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi HV RBR G17 G5 G11 G10 G18 G13 DG WR ZSH.
  { exfalso. clear -Hn Hi. lia. }
  pose proof RBR as ((G2 & G3 & G4 & G8 & G9 & G23 & G26 & G27) & G19 & G20 & G30).
  unfold PNADD.SH, PNADD.SBv in G23, G19, ZSH.
  pose proof (PNDF.dg_range V (i + 1)) as Hd.
  assert (C : L5.u32_at RSEGS M (F + 36 + 4 * i) (PNDF.dg V (i + 1))).
  { pose proof (DG (i + 1) ltac:(clear -Hi; lia)) as C. unfold PNADD.cell in C. replace (F + 36 + 4 * i) with (F + 32 + 4 * (i + 1)) by (clear; lia). exact C. }
  assert (ZS : L5KA.zeros_at M ((F + 36 + 4 * i) / 8 + 2147450880) 1).
  { destruct (sh_cell (i + 1) ltac:(clear -Hi; lia)) as (j & Ej & Hj). replace (F + 36 + 4 * i) with (F + 32 + 4 * (i + 1)) by (clear; lia). rewrite Ej.
    apply (L5KA.zeros_at_sub M _ _ _ _ ZSH); clear -Hj; lia. }
  assert (AL : (F + 36 + 4 * i) mod 4 = 0).
  { pose proof (Z.div_mod F 32 ltac:(clear; lia)) as E. rewrite FF32, Z.add_0_r in E. rewrite E. replace (32 * (F / 32) + 36 + 4 * i) with ((8 * (F / 32) + 9 + i) * 4) by (clear; lia). apply Z.mod_mul. clear; lia. }
  (let T := type of (PNADP2.adkSC_conc fx R M (fun j => match j with 52%nat => F + 36 + 4 * i | 53%nat => PNDF.dg V (i + 1) | 54%nat => 36 - i | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkSC_conc fx R M (fun j => match j with 52%nat => F + 36 + 4 * i | 53%nat => PNDF.dg V (i + 1) | 54%nat => 36 - i | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A10 & A12 & A13 & A18 & Hz) | (MS1 & KS1 & A10 & A12 & A13 & A18 & Hnz) ]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1.
  - rewrite Z.sub_0_r, Z.mod_small in Hz by (clear -Hd; lia).
    assert (D0 : PNDF.dg V (i + 1) = 0) by (clear -Hz Hd; lia).
    pose proof (PNDF.dg_zero_step V (i + 1) ltac:(clear -FV; lia) ltac:(clear -Hi; lia) ltac:(replace (35 - (i + 1) + 1) with (35 - i) by (clear; lia); exact HV) D0) as HV'.
    assert (Hi' : i + 1 <= 34).
    { destruct (Z_lt_le_dec 34 (i + 1)) as [LT|LE]; [| exact LE]. exfalso.
      replace (35 - (i + 1)) with 0 in HV' by (clear -LT Hi; lia). clear -HV' FVp. cbn in HV'. lia. }
    destruct (IH fx1 R1 M (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hi'; lia) HV') as (fx2 & R2 & z & MS2 & SP & Hz2).
    + unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1.
    + keep1 KS1.
    + keep1 KS1.
    + keep1 KS1.
    + rewrite A10. f_equal. clear; lia.
    + rewrite A18. f_equal. clear; lia.
    + rewrite A13. f_equal. clear; lia.
    + exact DG.
    + exact WR.
    + unfold PNADD.SH, PNADD.SBv. exact ZSH.
    + exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2 Hi; lia].
  - exists fx1, R1, (i + 1). split; [exact MS1|].
    split; [| clear -Hi; lia]. unfold PNADD.stP.
    split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
    split; [rewrite A18; f_equal; clear; lia|]. split; [rewrite A13; f_equal; clear; lia|].
    split; [rewrite (KS1 17%nat) by inl; rewrite G17, (bvu_small E1 FE1); reflexivity|]. keep1 KS1.
Qed.

(* [comment removed for export] *)
Lemma scan (FVp : 0 < V) fx R M :
  getr R (reg 2) = Z_to_bv 64 (S - 256) -> getr R (reg 3) = getr R0 (reg 3) -> getr R (reg 4) = getr R0 (reg 4) ->
  getr R (reg 8) = Z_to_bv 64 S -> getr R (reg 9) = Z_to_bv 64 (S - 256) -> getr R (reg 18) = Z_to_bv 64 (F + 32) ->
  L5.u64_at RSEGS M (S - 240) 16383 -> L5.u64_at RSEGS M (S - 232) E1 -> L5.u64_at RSEGS M (S - 224) (first + sigma) -> L5.u64_at RSEGS M (S - 216) first -> L5.u64_at RSEGS M (S - 208) 2147450880 -> L5.u64_at RSEGS M (S - 200) F -> L5.u64_at RSEGS M (S - 192) F -> L5.u64_at RSEGS M (S - 184) ((F / 8) + 2147450880) -> L5.u64_at RSEGS M (S - 176) (first + 42) -> L5.u64_at RSEGS M (S - 168) (F + 32) ->
  digs M 0 -> L5.writable RSEGS M (S - 256) 256 -> L5KA.zeros_at M (PNADD.SH F + 4) 18 ->
  exists fx' R' z, msteps RSEGS (st fx R 0xb4268 M) (st fx' R' 0xb4294 M) /\ PNADD.stP R0 S F first sigma e14 z (36 - z) R' /\ 1 <= z <= 35.
Proof.
  intros G2 G3 G4 G8 G9 G18 K240 K232 K224 K216 K208 K200 K192 K184 K176 K168 DG WR ZSH.
  assert (C0 : L5.u32_at RSEGS M (F + 32) 0).
  { pose proof (DG 0 ltac:(clear; lia)) as C. unfold PNADD.cell in C. rewrite dg0 in C. replace (F + 32 + 4 * 0) with (F + 32) in C by (clear; lia). exact C. }
  (let T := type of (PNADP2.adkZ1_conc fx R M (fun j => match j with 55%nat => 0 | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkZ1_conc fx R M (fun j => match j with 55%nat => 0 | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A5 & A10 & A11 & A13 & A17 & A19 & A20 & A23 & A26 & A27 & A30 & Hz) | (MS1 & KS1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnz) ]).
  2:{ exfalso. clear -Hnz. rewrite Z.sub_0_r, Z.mod_small in Hnz by lia. lia. }
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  pose proof V_lt35 as HV.
  destruct (scan_loop FVp 35%nat fx1 R1 M 0 eq_refl ltac:(clear; lia) ltac:(replace (35 - 0) with 35 by (clear; lia); exact HV)) as (fx2 & R2 & z & MS2 & SP & Hz2).
  - unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; first [ keep1 KS1 | assumption ].
  - exact A17.
  - exact A5.
  - exact A11.
  - rewrite A10. f_equal. clear; lia.
  - rewrite (KS1 18%nat) by inl. rewrite G18. f_equal. clear; lia.
  - rewrite A13; try (f_equal; clear; lia).
  - exact DG.
  - exact WR.
  - exact ZSH.
  - exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iszero fx R M e :
  PNADD.stZ R0 S F first sigma e R -> getr R (reg 17) = Z_to_bv 64 E1 -> L5.writable RSEGS M (S - 256) 256 -> L5.writable RSEGS M F 512 ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb425c M) (st fx' R' 0xb4294 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADD.stP R0 S F first sigma e 0 1 R' /\ cell M' 0 0.
Proof.
  intros (((G2 & G3 & G4 & G8 & G9 & G23 & G26 & G27) & G19 & G20 & G30) & G18 & A17 & G5) G17 WR WF.
  unfold PNADD.SH, PNADD.SBv in G23, G19.
  (let T := type of (PNADP2.adkZ0_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkZ0_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A13 & A25 & C0).
  exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
  split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  split. { unfold PNADD.stP. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
           split; [rewrite (KS1 18%nat) by inl; rewrite G18; f_equal; clear; lia|]. split; [exact A13|].
           split; [rewrite (KS1 17%nat) by inl; exact A17|]. keep1 KS1. }
  unfold PNADD.cell. replace (F + 32 + 4 * 0) with (F + 32) by (clear; lia). exact C0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Decode.
Variables (vp hi lo : Z).
Hypothesis Fvp : 6905856 <= vp <= 140737488355312.
Hypothesis Fvp8 : vp mod 8 = 0.
Hypothesis FvpSH : 2147446784 + 17592186048512 <= vp \/ vp + 16 <= 2147446784.
Hypothesis FvpS : S - 256 + 256 <= vp \/ vp + 16 <= S - 256.
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Hypothesis HV : V = (hi mod 2 ^ 49) * 2 ^ 64 + lo.
Hypothesis HE1 : E1 = hi / 4294967296 / 131072.
Definition Wdec (a : Z) : Prop := S - 240 <= a < S - 176 \/ S - 168 <= a < S - 160 \/ S - 136 <= a < S - 120.
Definition fcells (M : mem) : Prop :=
  L5.u64_at RSEGS M (S - 240) 16383 /\ L5.u64_at RSEGS M (S - 232) E1 /\ L5.u64_at RSEGS M (S - 224) (first + sigma) /\ L5.u64_at RSEGS M (S - 216) first
  /\ L5.u64_at RSEGS M (S - 208) 2147450880 /\ L5.u64_at RSEGS M (S - 200) F /\ L5.u64_at RSEGS M (S - 192) F /\ L5.u64_at RSEGS M (S - 184) ((F / 8) + 2147450880).

Lemma decode fx R M :
  PNADD.stJ R0 S F first sigma vp R -> L5.writable RSEGS M (S - 256) 256 -> L5.img_clear M 65536 1282048 -> zers M 4 -> PNADD.vp_at M vp lo hi ->
  exists fx' R' M', mem_grows M M' /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wdec a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ ((msteps RSEGS (st fx R 0xb406c M) (st fx' R' 0xb4994 M') /\ PNADD.stX R0 S F first sigma hi lo R')
        \/ (msteps RSEGS (st fx R 0xb406c M) (st fx' R' 0xb425c M') /\ PNADD.stZ R0 S F first sigma e14 R' /\ getr R' (reg 17) = Z_to_bv 64 E1)
        \/ (msteps RSEGS (st fx R 0xb406c M) (st fx' R' 0xb4164 M') /\ HD R' M' 3 /\ fcells M' /\ 0 < V)).
Proof.
  intros (((G2 & G3 & G4 & G8 & G9 & G23 & G26 & G27) & G19 & G20 & G30) & G18 & G24 & G10 & G11) WR IC ZR (VP0 & VP8 & VPZ).
  unfold PNADD.SH, PNADD.SBv in G23, G19, G11, VPZ.
  destruct (PNDBV.hi_fields hi Fhi) as (a & b & c & d & E & Ha & Hb & Hc & Hd).
  pose proof (PNADBV.msb_range hi lo Fhi Flo) as Hm. pose proof (PNADBV.hi32_range hi lo Fhi Flo) as Hh.
  (let T := type of (PNADP2.adkD1_conc fx R M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkD1_conc fx R M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & CND) | (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & CND) ]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1.
  2:{ exists fx1, R1, M. split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. left. split; [exact MS1|].
    unfold PNADD.stX. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
    split; [keep1 KS1|]. split; [exact A11|]. split; [exact A10|]. exact A13. }
  assert (B12 : getr R1 (reg 12) = Z_to_bv 64 (PNADBV.msb hi)) by (apply to_bv_of_unsigned; rewrite A12; reflexivity).
  assert (B13 : getr R1 (reg 13) = Z_to_bv 64 (PNADBV.hi32 hi)) by (rewrite A13; reflexivity).
  assert (RBO1 : PNADD.RBO R0 S F first sigma R1) by (unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv; repeat split; keep1 KS1).
  assert (B18 : getr R1 (reg 18) = Z_to_bv 64 (F + 32)) by keep1 KS1.
  assert (B24 : getr R1 (reg 24) = Z_to_bv 64 vp) by keep1 KS1.
  clear G2 G3 G4 G8 G9 G18 G19 G26 G27 G20 G23 G30 G24 G10 G11 KS1 A12 A13 A14 CND.
  pose proof RBO1 as ((G2 & G3 & G4 & G8 & G9 & G23 & G26 & G27) & G19 & G20 & G30).
  unfold PNADD.SH, PNADD.SBv in G23, G19.
  (let T := type of (PNADP2.adkD2_conc fx1 R1 M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | 37%nat => PNADBV.msb hi | 39%nat => PNADBV.hi32 hi | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkD2_conc fx1 R1 M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | 37%nat => PNADBV.msb hi | 39%nat => PNADBV.hi32 hi | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  assert (EE1 : PNADBV.hi32 hi / 131072 = E1) by (rewrite HE1; reflexivity).
  rewrite EE1 in P. clear A10 A11 B12 B13.
  assert (P0 : PNSDRN2.p0 V = 2 ^ 14 * b + c) by (unfold PNSDRN2.p0; rewrite HV, (PNDBV.f_p0 hi a b c d E Ha Hb Hc Hd lo Flo); reflexivity).
  assert (P1 : PNSDRN2.p1 V = hi mod 2 ^ 32).
  { unfold PNSDRN2.p1; rewrite HV, (PNDBV.f_mod49 hi a b c d E Ha Hb Hc Hd), (PNDBV.f_mod32 hi a b c d E Ha Hb Hc Hd).
    replace ((2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64 + lo) with (lo + (2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64) by (clear; lia).
    rewrite Z.div_add by (clear; lia); rewrite (Z.div_small lo) by exact Flo; rewrite Z.add_0_l.
    symmetry; apply (Z.mod_unique_pos _ _ (2 ^ 14 * b + c)); clear -Hb Hc Hd; lia. }
  assert (P2 : PNSDRN2.p2 V = lo / 2 ^ 32).
  { unfold PNSDRN2.p2. rewrite HV.
    pose proof (Z.div_mod lo (2 ^ 32) ltac:(clear; lia)) as EL; pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(clear; lia)) as BL.
    assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; clear -Flo; lia| apply Z.div_lt_upper_bound; [clear; lia| change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); clear -Flo; lia]]).
    replace ((hi mod 2 ^ 49 * 2 ^ 64 + lo) / 2 ^ 32) with ((hi mod 2 ^ 49) * 2 ^ 32 + lo / 2 ^ 32) by (apply (Z.div_unique_pos _ _ _ (lo mod 2 ^ 32)); clear -EL BL; lia).
    replace (hi mod 2 ^ 49 * 2 ^ 32 + lo / 2 ^ 32) with (lo / 2 ^ 32 + hi mod 2 ^ 49 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). apply Z.mod_small. exact QL. }
  assert (P3 : PNSDRN2.p3 V = lo mod 2 ^ 32).
  { unfold PNSDRN2.p3. rewrite HV. replace (hi mod 2 ^ 49 * 2 ^ 64 + lo) with (lo + (hi mod 2 ^ 49 * 2 ^ 32) * 2 ^ 32) by (clear; lia). rewrite Z.mod_add; [reflexivity| clear; lia]. }
  assert (QB : 0 <= lo / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; clear -Flo; lia| apply Z.div_lt_upper_bound; [clear; lia| change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); clear -Flo; lia]]).
  pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(clear; lia)) as BL. pose proof (Z.mod_pos_bound hi (2 ^ 32) ltac:(clear; lia)) as BH.
  pose proof (Z.mod_pos_bound hi (2 ^ 49) ltac:(clear; lia)) as B49.
  destruct P as (fx2 & R2 & M2 & MG2 & _ & FZ2 & [ (MS2 & KS2 & A5 & _ & _ & _ & _ & _ & A17 & _ & _ & _ & _ & _ & _ & _)
     | [ (MS2 & KS2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A20 & A22 & A23 & A25 & A26 & A27 & K168 & K184 & K192 & K200 & K208 & K216 & K224 & K232 & K240 & CQ & CND & _ & C124 & C128 & C132 & C136)
     | [ (MS2 & KS2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A20 & A22 & A23 & A25 & A26 & A27 & K168 & K184 & K192 & K200 & K208 & K216 & K224 & K232 & K240 & CND & _ & C124 & C128 & C132 & C136)
     | (MS2 & KS2 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A20 & A22 & A23 & A25 & A26 & A27 & K168 & K184 & K192 & K200 & K208 & K216 & K224 & K232 & K240 & CQ & C124 & C128 & C132 & C136) ] ] ]);
    (exists fx2, R2, M2; split; [exact MG2|]; split; [intros a0 Ha0 Hn; apply FZ2; [exact Ha0| intro W0; apply Hn; unfold Wdec; clear -W0; lia..]|]).
  { right; left. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [| exact A17].
    unfold PNADD.stZ. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS2. }
    split; [keep1 KS2|]. split; [rewrite A17, (bvu_small E1 FE1); reflexivity| exact A5]. }
  all: right; right; (split; [eapply msteps_trans; [exact MS1| exact MS2]|]).
  1: assert (Vnz : 0 < V) by (pose proof (PNADBV.w_nonzero _ (AX2.EVar 35) CQ) as NZ; cbn [AX2.edenot AX2.ev] in NZ; rewrite (PNDBV.u_lit lo Flo) in NZ; rewrite HV; clear -NZ Flo B49; assert (lo <> 0) by (intro Z0; apply NZ; rewrite Z0; reflexivity); lia).
  2: assert (Vnz : 0 < V) by (rewrite Z.sub_0_r in CND; pose proof (Z.mul_div_le lo 4294967296 ltac:(clear; lia)) as MD; pose proof (Z.div_pos lo 4294967296 ltac:(clear -Flo; lia) ltac:(clear; lia)) as DP; rewrite Z.mod_small in CND by (split; [exact DP| apply Z.div_lt_upper_bound; clear -Flo; lia]); rewrite HV; clear -CND MD Flo B49; lia).
  3: assert (Vnz : 0 < V) by (pose proof (PNADBV.w_nonzero _ PNADBV.XA CQ) as NZ; rewrite (PNADBV.XA_val hi lo Fhi Flo) in NZ by reflexivity; pose proof (PNADBV.A_nz hi lo Fhi Flo NZ) as NZ2; rewrite <- HV in NZ2; clear -NZ2 FV; lia).
  all: split; [| split; [| exact Vnz]].
  all: try solve [unfold fcells; repeat split; first [ assumption | (unfold PNADD.SH, PNADD.SBv in *; assumption) ]].
  all: unfold PNADRN3.HD; split; [unfold PNADRN.RRa; repeat split; first [ keep1 KS2 | fsc ]|].
  all: rewrite PNSDRN2.Wk3; rewrite P0, P1, P2, P3.
  all: unfold PNADBV.msb, PNADBV.hi32 in C136; rewrite (PNDBV.f_parts0 hi a b c d E Ha Hb Hc Hd) in C136.
  all: rewrite <- (PNMW.u32_at_mod RSEGS M2 (S - 132) hi) in C132; rewrite <- (PNMW.u32_at_mod RSEGS M2 (S - 124) lo) in C124.
  all: split; [apply (PNMW.u64_of_u32x2 _ _ (S - 136)); [clear -FS; lia| clear -FS; lia| clear -Hb Hc; lia| exact BH| exact C136| replace (S - 136 + 4) with (S - 132) by (clear; lia); exact C132]|].
  all: split; [apply (PNMW.u64_of_u32x2 _ _ (S - 128)); [clear -FS; lia| clear -FS; lia| exact QB| exact BL| exact C128| replace (S - 128 + 4) with (S - 124) by (clear; lia); exact C124]|].
  all: split; [exact K168|].
  all: split; [intros i Hi; clear -Hi; lia|].
  all: intros i Hi; unfold PNADD.cell; apply (PNMW.u32_at_agree _ M); [intros j Hj; apply FZ2; [clear -Hj Hi FF1; lia| intro W0; clear -W0 Hj Hi FFS FS FF1; lia ..]| clear -Hi FF1; lia| clear -Hi FF1; lia| exact (ZR i ltac:(clear -Hi; lia))].
Qed.
End Decode.

End Call.
End PNADMID.
