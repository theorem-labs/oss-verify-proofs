(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3 MuslStrlen.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablRep TablStmts TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablImgU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition SL_ENTRY : Z := 0xe3600.
Definition SL_HEAD  : Z := 0xe361c.
Definition SL_ALGN  : Z := 0xe363c.
Definition SL_WORD  : Z := 0xe3654.
Definition SL_TAIL  : Z := 0xe3670.
Definition SL_END   : Z := 0xe3680.
Definition SL_RET0  : Z := 0xe3688.
Definition SL_STOPS : list Z := [SL_HEAD; SL_ALGN; SL_WORD; SL_TAIL; SL_END; SL_RET0].

Definition C1 : Z := 72340172838076672.
Definition Tc (x : Z) : Z := Z.land (Z.lor ((C1 - x) mod 2 ^ 64) x) HZ.HIGHS.

Lemma testbit_mod64 : forall a i, 0 <= i < 64 -> Z.testbit (a mod 2 ^ 64) i = Z.testbit a i.
Proof. intros a i Hi. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.testbit_ones_nonneg by lia.
  replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia). apply andb_true_r. Qed.

Lemma HIGHS_high : forall i, 64 <= i -> Z.testbit HZ.HIGHS i = false.
Proof. intros i Hi. apply Z.bits_above_log2; [unfold HZ.HIGHS; lia|]. unfold HZ.HIGHS.
  eapply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; [lia|]. cbn. lia. Qed.

Lemma Tc_Tz : forall x, 0 <= x < 2 ^ 64 -> Z.lxor (Tc x) HZ.HIGHS = HZ.Tz x.
Proof.
  intros x Hx. unfold Tc, HZ.Tz. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !Z.land_spec, Z.lor_spec, Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - rewrite !testbit_mod64 by lia.
    replace (Z.testbit HZ.ALLONES i) with true.
    2:{ unfold HZ.ALLONES. change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia. symmetry; apply Z.ltb_lt; lia. }
    assert (E : Z.testbit (C1 - x) i = negb (Z.testbit (x + HZ.ONESNEG) i)).
    { replace (C1 - x) with (Z.lnot (x + HZ.ONESNEG) + 2 ^ 64) by (unfold Z.lnot, C1, HZ.ONESNEG; lia).
      rewrite <- (testbit_mod64 (Z.lnot (x + HZ.ONESNEG) + 2 ^ 64)) by lia.
      rewrite <- Zplus_mod_idemp_r, Z_mod_same_full, Z.add_0_r, testbit_mod64 by lia.
      apply Z.lnot_spec. lia. }
    rewrite E. destruct (Z.testbit (x + HZ.ONESNEG) i), (Z.testbit x i), (Z.testbit HZ.HIGHS i); reflexivity.
  - rewrite !HIGHS_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

Lemma Tc_iff : forall x, 0 <= x < 2 ^ 64 -> (Tc x = HZ.HIGHS <-> HZ.Tz x = 0).
Proof.
  intros x Hx. rewrite <- Tc_Tz by lia. split; intros H.
  - rewrite H. apply Z.lxor_nilpotent.
  - apply Z.lxor_eq. exact H.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma word_test_val : forall W : word,
  bv_unsigned (alu64 ALU_AND (alu64 ALU_OR (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) W) (Z_to_bv 64 C1)) W)
                         (Z_to_bv 64 HZ.HIGHS)) = Tc (bv_unsigned W).
Proof.
  intros W. pose proof (bv_unsigned_in_range _ W) as HW. unfold bv_modulus in HW.
  cbn [alu64 alu mul_div]. unfold Tc.
  rewrite bv_and_unsigned, bv_or_unsigned, bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in HW.
  f_equal. f_equal.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). unfold C1. nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition dn8 (a : Z) : Z := a - a mod 8.
Definition up8 (a : Z) : Z := a + (8 - a mod 8) mod 8.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma dn8_le : forall a, dn8 a <= a /\ a < dn8 a + 8 /\ dn8 a mod 8 = 0.
Proof. intros a. unfold dn8. lia. Qed.
Lemma up8_ge : forall a, a <= up8 a /\ up8 a < a + 8 /\ up8 a mod 8 = 0.
Proof. intros a. unfold up8. lia. Qed.
Lemma dn8_mono : forall a b, a <= b -> dn8 a <= dn8 b.
Proof. intros a b H. unfold dn8. lia. Qed.
Lemma dn8_of_aligned : forall a, a mod 8 = 0 -> dn8 a = a.
Proof. intros a H. unfold dn8. lia. Qed.
Lemma aligned_le_dn8 : forall q a, q mod 8 = 0 -> q <= a -> q <= dn8 a.
Proof. intros q a H H'. unfold dn8. lia. Qed.
Lemma up8_dn8 : forall a, up8 (a + 1) = dn8 a + 8.
Proof. intros a. unfold up8, dn8. lia. Qed.
Lemma aligned_lt_le8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> a < b -> a + 8 <= b.
Proof. intros a b Ha Hb H. lia. Qed.
Lemma aligned_next : forall a, a mod 8 = 0 -> (a + 8) mod 8 = 0.
Proof. intros a Ha. lia. Qed.
Lemma mod8_dec : forall a, 0 <= a -> a mod 8 = 0 \/ a mod 8 <> 0.
Proof. intros a Ha. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma sub_mod_val : forall p n, 0 <= p -> 0 <= n -> p + n < 2 ^ 64 ->
  (((-1) mod 2 ^ 64 * (p mod 2 ^ 64)) mod 2 ^ 64 + (p + n) mod 2 ^ 64) mod 2 ^ 64 = n mod 2 ^ 64.
Proof.
  intros p n Hp Hn Hpn. rewrite (Z.mod_small p), (Z.mod_small (p + n)) by lia.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace ((2 ^ 64 - 1) * p) with (- p + p * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Ltac sub_mod_tac p n := first [apply sub_mod_val; lia | match goal with |- ?g => idtac "SUBMOD" g; fail end].

Section Strlen.
  Context {fx : FPState}.
  Variables (M : mem) (p n : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis CS : ro_cstr SEGS L p n.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).

  Lemma cs_bounds : 0x10000 <= p /\ 0 <= n /\ p + n + 8 <= 2 ^ 47.
  Proof using p n CS. destruct CS as (A & B & C & _). lia. Qed.

  Lemma str_byte : forall i, 0 <= i < n -> exists c, 0 < c < 256 /\ cellw SEGS M (p + i) 1 c.
  Proof using M p n HRO CS.
    intros i Hi. destruct CS as (_ & _ & _ & HM). destruct (HM M HRO) as (S & _ & _).
    destruct (S i Hi) as (c & Hc & F). exists c. split; [exact Hc|]. split; [cbn; lia | exact F].
  Qed.
  Lemma nul_byte : cellw SEGS M (p + n) 1 0.
  Proof using M p n HRO CS.
    destruct CS as (_ & _ & _ & HM). destruct (HM M HRO) as (_ & Z0 & _). split; [cbn; lia | exact Z0].
  Qed.

  Lemma env_byte : forall a, dn8 p <= a < up8 (p + n + 1) -> exists c, 0 <= c < 256 /\ cellw SEGS M a 1 c.
  Proof using M p n HRO CS.
    intros a Ha. destruct CS as (_ & _ & _ & HM). destruct (HM M HRO) as (_ & _ & RD).
    destruct (RD a ltac:(unfold dn8, up8 in Ha; lia)) as (c & Hc & F). exists c. split; [lia|]. split; [cbn; lia | exact F].
  Qed.

  Lemma word_at : forall A, dn8 p <= A -> A + 8 <= up8 (p + n + 1) ->
    exists cs, length cs = 8%nat /\ cellw SEGS M A 8 (bytes_le_to_Z (str_bytes cs)) /\
      (forall i, (i < 8)%nat -> HZ.zb (bytes_le_to_Z (str_bytes cs)) i = Znth (Z.of_nat i) cs /\ 0 <= Znth (Z.of_nat i) cs < 256) /\
      (forall i, (i < 8)%nat -> p <= A + Z.of_nat i < p + n -> Znth (Z.of_nat i) cs <> 0) /\
      (forall i, (i < 8)%nat -> A + Z.of_nat i = p + n -> Znth (Z.of_nat i) cs = 0).
  Proof using M p n HRO CS.
    intros A HA0 HA1. pose proof cs_bounds as (Bp & Bn & Bpn). pose proof (dn8_le p) as (D1 & D2 & D3).
    pose proof (up8_ge (p + n + 1)) as (U1 & U2 & U3).

    assert (B : forall i, 0 <= i < 8 -> exists c, 0 <= c < 256 /\ cellw SEGS M (A + i) 1 c).
    { intros i Hi. destruct (env_byte (A + i) ltac:(lia)) as (c & Hc & Cc). exists c. split; [exact Hc | exact Cc]. }
    destruct (B 0 ltac:(lia)) as (c0 & R0 & C0). destruct (B 1 ltac:(lia)) as (c1 & R1 & C1').
    destruct (B 2 ltac:(lia)) as (c2 & R2 & C2). destruct (B 3 ltac:(lia)) as (c3 & R3 & C3).
    destruct (B 4 ltac:(lia)) as (c4 & R4 & C4). destruct (B 5 ltac:(lia)) as (c5 & R5 & C5).
    destruct (B 6 ltac:(lia)) as (c6 & R6 & C6). destruct (B 7 ltac:(lia)) as (c7 & R7 & C7).
    set (cs := [c0; c1; c2; c3; c4; c5; c6; c7]).
    assert (CI : forall i, 0 <= i < 8 -> 0 <= Znth i cs < 256 /\ cellw SEGS M (A + i) 1 (Znth i cs)).
    { intros i Hi.
      assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; unfold Znth; subst cs;
        [ change (nth (Z.to_nat 0) _ 0) with c0 | change (nth (Z.to_nat 1) _ 0) with c1
        | change (nth (Z.to_nat 2) _ 0) with c2 | change (nth (Z.to_nat 3) _ 0) with c3
        | change (nth (Z.to_nat 4) _ 0) with c4 | change (nth (Z.to_nat 5) _ 0) with c5
        | change (nth (Z.to_nat 6) _ 0) with c6 | change (nth (Z.to_nat 7) _ 0) with c7 ]; split; assumption. }
    exists cs. split; [reflexivity|].
    assert (HF : forall i, 0 <= i < Zlen cs -> 0 <= Znth i cs < 256 /\ CRep.fld SEGS M (A + i) 1 (Znth i cs)).
    { intros i Hi. change (Zlen cs) with 8 in Hi. destruct (CI i Hi) as [X [_ Y]]. split; [exact X | exact Y]. }
    pose proof (fld_str_rdn SEGS M A cs ltac:(lia) ltac:(change (Zlen cs) with 8; lia) HF) as RD8.
    change (length cs) with 8%nat in RD8.
    pose proof (bytes_le_to_Z_range (str_bytes cs) eq_refl) as VR.
    split.
    { split.
      - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      - change (N.to_nat 8) with 8%nat. rewrite (SymDrive3.word_to_le_bytes_of_lez 8 (str_bytes cs) (eq_refl : length (str_bytes cs) = 8%nat) ltac:(lia)). exact RD8. }
    assert (ZB : forall i, (i < 8)%nat -> HZ.zb (bytes_le_to_Z (str_bytes cs)) i = Znth (Z.of_nat i) cs).
    { intros i Hi. rewrite zb_of_bytes by (subst cs; cbn; lia).
      destruct (CI (Z.of_nat i) ltac:(lia)) as [X _].
      unfold str_bytes. replace (Z_to_bv 8 0) with ((fun c => Z_to_bv 8 c) 0) by reflexivity.
      rewrite map_nth. unfold Znth in *. rewrite Nat2Z.id in *. apply u8_of_Z. exact X. }
    split.
    { intros i Hi. split; [apply ZB, Hi|]. apply (CI (Z.of_nat i)). lia. }
    split.
    { intros i Hi Hin. destruct (CI (Z.of_nat i) ltac:(lia)) as [_ Ci].
      destruct (str_byte (A + Z.of_nat i - p) ltac:(lia)) as (c' & Hc' & Cc').
      replace (p + (A + Z.of_nat i - p)) with (A + Z.of_nat i) in Cc' by lia.
      pose proof (cell1_inj SEGS M _ _ _ Ci Cc'). lia. }
    { intros i Hi Heq. destruct (CI (Z.of_nat i) ltac:(lia)) as [_ Ci]. rewrite Heq in Ci.
      exact (cell1_inj SEGS M _ _ _ Ci nul_byte). }
  Qed.

  Definition keptA (R R' : bvmap 5 word) : Prop := kept R R' /\ getr R' 10%bv = getr R 10%bv.
  Lemma keptA_trans : forall R1 R2 R3, keptA R1 R2 -> keptA R2 R3 -> keptA R1 R3.
  Proof using. intros R1 R2 R3 [A B] [C D]. split; [exact (keeps_cs_trans _ _ _ A C) | congruence]. Qed.
  Lemma keptA_refl : forall R, keptA R R.
  Proof using. intros R. split; [apply keeps_cs_refl | reflexivity]. Qed.
  Ltac keptA_of HR' := split; [exact (kept_of_syms _ _ _ _ HR' eq_refl) | let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; symmetry; assumption]].

  Lemma tail_step : forall R t c,
    p <= t <= p + n -> cellw SEGS M t 1 c -> 0 <= c < 256 ->
    getr R 12%bv = Z_to_bv 64 t -> getr R 11%bv = Z_to_bv 64 (t - 1) ->
    exists R', keptA R R' /\
      ( (c <> 0 /\ msteps SEGS (st R SL_TAIL) (st R' SL_TAIL) /\ getr R' 12%bv = Z_to_bv 64 (t + 1) /\ getr R' 11%bv = Z_to_bv 64 t)
      \/ (c = 0 /\ msteps SEGS (st R SL_TAIL) (st R' SL_END) /\ getr R' 11%bv = Z_to_bv 64 t) ).
  Proof using fx M p n CS.
    intros R t c Ht Cc Hc H12 H11. pose proof cs_bounds as (Bp & Bn & Bpn).
    pose (E := Eseed R [Z_to_bv 64 t; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id [(12%bv, EVar 32); (11%bv, EAlu ALU_ADD (EVar 32) (ELit (-1)))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; [exact H12|].
      rewrite H11. rewrite w_addm by lia. reflexivity. }
    assert (HK : know_ok SEGS E M []) by constructor.
    destruct (Z.eq_dec c 0) as [Hz|Hnz].
    - xrun HR HK 20%nat SL_STOPS (SCR [false] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [sc_rd Cc | sc_br]. }
      exists R'. split; [keptA_of HR'|]. right. split; [exact Hz|]. split; [exact Hms|].
      rreg HR' 11%bv H11'. rewrite H11'. reflexivity.
    - xrun HR HK 20%nat SL_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [sc_rd Cc | sc_br]. }
      exists R'. split; [keptA_of HR'|]. left. split; [exact Hnz|]. split; [exact Hms|].
      rreg HR' 12%bv H12'. rreg HR' 11%bv H11'. rewrite H12', H11'. split; [rewrite w_add by lia|]; reflexivity.
  Qed.

  Lemma tail_loop : forall k R t,
    t = p + n - Z.of_nat k -> p <= t ->
    getr R 12%bv = Z_to_bv 64 t -> getr R 11%bv = Z_to_bv 64 (t - 1) ->
    exists R', keptA R R' /\ msteps SEGS (st R SL_TAIL) (st R' SL_END) /\ getr R' 11%bv = Z_to_bv 64 (p + n).
  Proof using fx M p n HRO CS.
    induction k as [|k IH]; intros R t Ht Hpt H12 H11.
    - assert (Et : t = p + n) by lia. rewrite Et in H12, H11.
      destruct (tail_step R (p + n) 0 ltac:(lia) nul_byte ltac:(lia) H12 H11) as (R' & K & [[C _]|(_ & MS & H11')]); [lia|].
      exists R'. split; [exact K|]. split; [exact MS | exact H11'].
    - destruct (str_byte (t - p) ltac:(lia)) as (c & Hc & Cc). replace (p + (t - p)) with t in Cc by lia.
      destruct (tail_step R t c ltac:(lia) Cc ltac:(lia) H12 H11) as (R1 & K1 & [(_ & MS1 & H12' & H11')|[C _]]); [|lia].
      destruct (IH R1 (t + 1) ltac:(lia) ltac:(lia) H12' ltac:(rewrite H11'; f_equal; lia)) as (R' & K' & MS' & H11'').
      exists R'. split; [exact (keptA_trans _ _ _ K1 K')|]. split; [|exact H11''].
      eapply msteps_trans; [exact MS1 | exact MS'].
  Qed.

  Lemma word_step : forall R A,
    p <= A -> A mod 8 = 0 -> A <= dn8 (p + n) ->
    getr R 12%bv = Z_to_bv 64 (A - 8) -> getr R 11%bv = Z_to_bv 64 (A - 9) ->
    getr R 13%bv = Z_to_bv 64 C1 -> getr R 14%bv = Z_to_bv 64 HZ.HIGHS ->
    exists R', keptA R R' /\ getr R' 13%bv = Z_to_bv 64 C1 /\ getr R' 14%bv = Z_to_bv 64 HZ.HIGHS /\
      ( (A + 8 <= p + n /\ msteps SEGS (st R SL_WORD) (st R' SL_WORD) /\ getr R' 12%bv = Z_to_bv 64 A /\ getr R' 11%bv = Z_to_bv 64 (A - 1))
      \/ (A = dn8 (p + n) /\ msteps SEGS (st R SL_WORD) (st R' SL_TAIL) /\ getr R' 12%bv = Z_to_bv 64 A /\ getr R' 11%bv = Z_to_bv 64 (A - 1)) ).
  Proof using fx M p n HRO CS.
    intros R A HpA HA8 HAd H12 H11 H13 H14. pose proof cs_bounds as (Bp & Bn & Bpn).
    pose proof (dn8_le (p + n)) as (D1 & D2 & D3). pose proof (dn8_le p) as (E1 & E2 & E3). pose proof (up8_dn8 (p + n)) as U.
    destruct (word_at A ltac:(pose proof (dn8_mono p A HpA); rewrite (dn8_of_aligned A HA8) in *; lia) ltac:(lia)) as (cs & Hlen & CW & ZB & NZ & ZZ).
    set (W := bytes_le_to_Z (str_bytes cs)) in *.
    pose proof (proj1 CW) as WR. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in WR.
    pose (E := Eseed R [Z_to_bv 64 (A - 8); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 W]).
    assert (HR : regs_ok E (srs sr_id [(12%bv, EVar 32); (11%bv, EAlu ALU_ADD (EVar 32) (ELit (-1))); (13%bv, ELit C1); (14%bv, ELit HZ.HIGHS)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; [exact H12| |exact H13|exact H14].
      rewrite H11. rewrite w_addm by lia. f_equal. lia. }
    assert (HK : know_ok SEGS E M []) by constructor.

    assert (TEST : forall b : bool,
      (if b then HZ.Tz W = 0 else HZ.Tz W <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ
        (EAlu ALU_AND (EAlu ALU_OR (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 40)) (ELit C1)) (EVar 40)) (ELit HZ.HIGHS))
        (ELit HZ.HIGHS))).
    { intros b Hb. cbn [sc_denot]. cbn [branch_taken]. unfold bv_eqb. evs. rewrite word_test_val.
      rewrite (u64_of_Z W) by lia. rewrite u64_of_Z by (unfold HZ.HIGHS; lia).
      destruct b; [apply Z.eqb_eq; apply (proj2 (Tc_iff W WR)); exact Hb | apply Z.eqb_neq; intros C; apply Hb; apply (proj1 (Tc_iff W WR)); exact C]. }
    destruct (Z_lt_le_dec A (dn8 (p + n))) as [Hlt|Hge].
    -
      assert (HA8' : A + 8 <= dn8 (p + n)) by (apply aligned_lt_le8; assumption).
      xrun HR HK 20%nat SL_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [sc_rd CW | apply TEST | idtac].
        - apply (HZ.Tz_nozero W WR). intros i Hi. rewrite (proj1 (ZB i Hi)). apply NZ; [exact Hi | lia].
 }
      exists R'. split; [keptA_of HR'|]. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'. split; [exact H13'|]. split; [exact H14'|].
      left. split; [lia|]. split; [exact Hms|].
      rreg HR' 12%bv H12'. rreg HR' 11%bv H11'. rewrite H12', H11'. split; (repeat first [rewrite w_add by lia | rewrite w_addm by lia]); f_equal; lia.
    - assert (HAe : A = dn8 (p + n)) by lia.
      xrun HR HK 20%nat SL_STOPS (SCR [false] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [sc_rd CW | apply TEST | idtac].
        - apply (HZ.Tz_haszero W (Z.to_nat (p + n - A)) WR ltac:(lia)).
          + rewrite (proj1 (ZB (Z.to_nat (p + n - A)) ltac:(lia))). apply ZZ; lia.
          + intros j Hj. rewrite (proj1 (ZB j ltac:(lia))). apply NZ; lia.
 }
      exists R'. split; [keptA_of HR'|]. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'. split; [exact H13'|]. split; [exact H14'|].
      right. split; [exact HAe|]. split; [exact Hms|].
      rreg HR' 12%bv H12'. rreg HR' 11%bv H11'. rewrite H12', H11'. split; (repeat first [rewrite w_add by lia | rewrite w_addm by lia]); f_equal; lia.
  Qed.

  Lemma word_loop : forall k R A,
    A = dn8 (p + n) - 8 * Z.of_nat k -> p <= A -> A mod 8 = 0 ->
    getr R 12%bv = Z_to_bv 64 (A - 8) -> getr R 11%bv = Z_to_bv 64 (A - 9) ->
    getr R 13%bv = Z_to_bv 64 C1 -> getr R 14%bv = Z_to_bv 64 HZ.HIGHS ->
    exists R', keptA R R' /\ msteps SEGS (st R SL_WORD) (st R' SL_TAIL) /\
      getr R' 12%bv = Z_to_bv 64 (dn8 (p + n)) /\ getr R' 11%bv = Z_to_bv 64 (dn8 (p + n) - 1).
  Proof using fx M p n HRO CS.
    induction k as [|k IH]; intros R A HA HpA HA8 H12 H11 H13 H14.
    - destruct (word_step R A HpA HA8 ltac:(lia) H12 H11 H13 H14) as (R' & K & _ & _ & [(C & _)|(E & MS & H12' & H11')]).
      + exfalso. pose proof (dn8_le (p + n)). lia.
      + exists R'. rewrite E in H12', H11'. auto.
    - destruct (word_step R A HpA HA8 ltac:(lia) H12 H11 H13 H14) as (R1 & K1 & H13' & H14' & [(C & MS1 & H12' & H11')|(E & _)]); [|lia].
      destruct (IH R1 (A + 8) ltac:(lia) ltac:(lia) (aligned_next A HA8)
                  ltac:(rewrite H12'; f_equal; lia) ltac:(rewrite H11'; f_equal; lia) H13' H14') as (R' & K' & MS' & H12'' & H11'').
      exists R'. split; [exact (keptA_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1 | exact MS']|]. auto.
  Qed.

  Lemma head_step : forall R i,
    0 <= i < n ->
    getr R 11%bv = Z_to_bv 64 (p + i) -> getr R 12%bv = Z_to_bv 64 (p + i + 1) ->
    exists R', keptA R R' /\
      ( ((p + i + 1) mod 8 = 0 /\ msteps SEGS (st R SL_HEAD) (st R' SL_ALGN) /\ getr R' 12%bv = Z_to_bv 64 (p + i + 1))
      \/ ((p + i + 1) mod 8 <> 0 /\ i + 1 < n /\ msteps SEGS (st R SL_HEAD) (st R' SL_HEAD)
           /\ getr R' 11%bv = Z_to_bv 64 (p + i + 1) /\ getr R' 12%bv = Z_to_bv 64 (p + i + 2))
      \/ ((p + i + 1) mod 8 <> 0 /\ i + 1 = n /\ msteps SEGS (st R SL_HEAD) (st R' SL_END) /\ getr R' 11%bv = Z_to_bv 64 (p + n)) ).
  Proof using fx M p n HRO CS.
    intros R i Hi H11 H12. pose proof cs_bounds as (Bp & Bn & Bpn).

    assert (HB : exists c, 0 <= c < 256 /\ cellw SEGS M (p + i + 1) 1 c /\ (c = 0 <-> i + 1 = n)).
    { destruct (Z.eq_dec (i + 1) n) as [E|NE].
      - exists 0. split; [lia|]. split; [rewrite <- Z.add_assoc, E; exact nul_byte | lia].
      - destruct (str_byte (i + 1) ltac:(lia)) as (c & Hc & Cc). exists c. rewrite Z.add_assoc in Cc. split; [lia|]. split; [exact Cc | lia]. }
    destruct HB as (c & Hc & Cc & Hcn).
    pose (E := Eseed R [Z_to_bv 64 (p + i); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id [(11%bv, EVar 32); (12%bv, EAlu ALU_ADD (EVar 32) (ELit 1))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; [exact H11|].
      rewrite H12. rewrite w_add by lia. reflexivity. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (ALN : forall b : bool, (if b then (p + i + 1) mod 8 = 0 else (p + i + 1) mod 8 <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ (EAlu ALU_AND (EAlu ALU_ADD (EVar 32) (ELit 1)) (ELit 7)) (ELit 0))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite w_add, w_and by lia. rewrite land7_mod by lia.
      pose proof (Z.mod_pos_bound (p + i + 1) 8 ltac:(lia)). rewrite br_eq by lia. destruct b; bool_lia. }
    destruct (mod8_dec (p + i + 1) ltac:(lia)) as [AL|NAL].
    - xrun HR HK 20%nat SL_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [apply ALN; exact AL | idtac]. }
      exists R'. split; [keptA_of HR'|]. left. split; [exact AL|]. split; [exact Hms|].
      rreg HR' 12%bv H12'. rewrite H12'. rewrite w_add by lia. reflexivity.
    - destruct (Z.eq_dec c 0) as [Hz|Hnz].
      + xrun HR HK 20%nat SL_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [apply ALN; exact NAL | sc_rd Cc | idtac]. }
        exists R'. split; [keptA_of HR'|]. right; right. split; [exact NAL|]. split; [lia|]. split; [exact Hms|].
        rreg HR' 11%bv H11'. rewrite H11'. rewrite w_add by lia. f_equal. lia.
      + xrun HR HK 20%nat SL_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [apply ALN; exact NAL | sc_rd Cc | idtac]. }
        exists R'. split; [keptA_of HR'|]. right; left. split; [exact NAL|]. split; [lia|]. split; [exact Hms|].
        rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rewrite H11', H12'. rewrite !w_add by lia. split; f_equal; lia.
  Qed.

  Lemma head_loop : forall k R i,
    i = n - 1 - Z.of_nat k -> 0 <= i ->
    getr R 11%bv = Z_to_bv 64 (p + i) -> getr R 12%bv = Z_to_bv 64 (p + i + 1) ->
    exists R', keptA R R' /\
      ( (exists q, q mod 8 = 0 /\ p <= q <= p + n /\ msteps SEGS (st R SL_HEAD) (st R' SL_ALGN) /\ getr R' 12%bv = Z_to_bv 64 q)
      \/ (msteps SEGS (st R SL_HEAD) (st R' SL_END) /\ getr R' 11%bv = Z_to_bv 64 (p + n)) ).
  Proof using fx M p n HRO CS.
    induction k as [|k IH]; intros R i Hi Hi0 H11 H12.
    - destruct (head_step R i ltac:(lia) H11 H12) as (R' & K & [(AL & MS & H12')|[(NAL & LT & _)|(NAL & EQ & MS & H11')]]); [ | lia | ].
      + exists R'. split; [exact K|]. left. exists (p + i + 1). split; [exact AL|]. split; [lia|]. auto.
      + exists R'. split; [exact K|]. right. auto.
    - destruct (head_step R i ltac:(lia) H11 H12) as (R1 & K1 & [(AL & MS & H12')|[(NAL & LT & MS1 & H11' & H12')|(NAL & EQ & _)]]); [ | | lia ].
      + exists R1. split; [exact K1|]. left. exists (p + i + 1). split; [exact AL|]. split; [lia|]. auto.
      + destruct (IH R1 (i + 1) ltac:(lia) ltac:(lia) ltac:(rewrite H11'; f_equal; lia) ltac:(rewrite H12'; f_equal; lia)) as (R' & K' & POST).
        exists R'. split; [exact (keptA_trans _ _ _ K1 K')|].
        destruct POST as [(q & Hq & Hpq & MS' & H12'')|(MS' & H11'')].
        * left. exists q. split; [exact Hq|]. split; [exact Hpq|]. split; [eapply msteps_trans; [exact MS1|exact MS']| exact H12''].
        * right. split; [eapply msteps_trans; [exact MS1|exact MS']| exact H11''].
  Qed.

  Lemma algn_block : forall R q,
    p <= q <= p + n -> q mod 8 = 0 -> getr R 12%bv = Z_to_bv 64 q ->
    exists R', keptA R R' /\ msteps SEGS (st R SL_ALGN) (st R' SL_WORD) /\
      getr R' 12%bv = Z_to_bv 64 (q - 8) /\ getr R' 11%bv = Z_to_bv 64 (q - 9) /\
      getr R' 13%bv = Z_to_bv 64 C1 /\ getr R' 14%bv = Z_to_bv 64 HZ.HIGHS.
  Proof using fx M p n HRO CS.
    intros R q Hq Hq8 H12. pose proof cs_bounds as (Bp & Bn & Bpn).
    pose (E := Eseed R [Z_to_bv 64 q]).
    assert (HR : regs_ok E (srs sr_id [(12%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact H12. }
    assert (HK : know_ok SEGS E M [KImg (ti_ro_lo Img.ti) (ti_ro_hi Img.ti)]).
    { constructor; [|constructor]. apply (kimg_ro SEGS L E M _ _ HRO Img.rodata); cbn; lia. }
    xrun HR HK 20%nat SL_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    exists R'. split; [keptA_of HR'|]. split; [exact Hms|].
    rreg HR' 12%bv H12'. rreg HR' 11%bv H11'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
    rewrite H12', H11', H13', H14'. rewrite !w_addm by lia. repeat split; reflexivity.
  Qed.

  Lemma entry_block : forall R,
    getr R 10%bv = Z_to_bv 64 p ->
    exists R', keptA R R' /\
      ( (p mod 8 = 0 /\ msteps SEGS (st R SL_ENTRY) (st R' SL_ALGN) /\ getr R' 12%bv = Z_to_bv 64 p)
      \/ (p mod 8 <> 0 /\ n = 0 /\ exists R'', msteps SEGS (st R SL_ENTRY) (st R'' 0xe368c) /\ kept R R'' /\ getr R'' 10%bv = Z_to_bv 64 0)
      \/ (p mod 8 <> 0 /\ 0 < n /\ msteps SEGS (st R SL_ENTRY) (st R' SL_HEAD) /\ getr R' 11%bv = Z_to_bv 64 p /\ getr R' 12%bv = Z_to_bv 64 (p + 1)) ).
  Proof using fx M p n HRO CS.
    intros R H10. pose proof cs_bounds as (Bp & Bn & Bpn).
    assert (HB : exists c, 0 <= c < 256 /\ cellw SEGS M p 1 c /\ (c = 0 <-> n = 0)).
    { destruct (Z.eq_dec n 0) as [E|NE].
      - exists 0. split; [lia|]. split; [pose proof nul_byte as NB; rewrite E, Z.add_0_r in NB; exact NB | lia].
      - destruct (str_byte 0 ltac:(lia)) as (c & Hc & Cc). rewrite Z.add_0_r in Cc. exists c. split; [lia|]. split; [exact Cc | lia]. }
    destruct HB as (c & Hc & Cc & Hcn).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 c]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact H10. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (ALN : forall b : bool, (if b then p mod 8 = 0 else p mod 8 <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ (EAlu ALU_AND (EVar 32) (ELit 7)) (ELit 0))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite w_and by lia. rewrite land7_mod by lia.
      pose proof (Z.mod_pos_bound p 8 ltac:(lia)). rewrite br_eq by lia. destruct b; bool_lia. }
    destruct (mod8_dec p ltac:(lia)) as [AL|NAL].
    - xrun HR HK 20%nat SL_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1; first [apply ALN; exact AL | idtac]. }
      exists R'. split; [keptA_of HR'|]. left. split; [exact AL|]. split; [exact Hms|].
      rreg HR' 12%bv H12'. exact H12'.
    - destruct (Z.eq_dec c 0) as [Hz|Hnz].
      + xrun HR HK 20%nat [SL_HEAD; SL_ALGN] (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [apply ALN; exact NAL | sc_rd Cc | idtac]. }
        exists R. split; [apply keptA_refl|]. right; left. split; [exact NAL|]. split; [lia|].
        exists R'. split; [exact Hms|]. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|].
        rreg HR' 10%bv H10'. exact H10'.
      + xrun HR HK 20%nat SL_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [apply ALN; exact NAL | sc_rd Cc | idtac]. }
        exists R'. split; [keptA_of HR'|]. right; right. split; [exact NAL|]. split; [lia|]. split; [exact Hms|].
        rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rewrite H11', H12'. rewrite w_add by lia. split; reflexivity.
  Qed.

  Lemma end_block : forall R (ret : word),
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (p + n) -> getr R 1%bv = ret -> ret_ok ret ->
    exists R', kept R R' /\ msteps SEGS (st R SL_END) (@mkst fx R' ret M (seg_rom SEGS)) /\ getr R' 10%bv = Z_to_bv 64 n.
  Proof using fx M p n CS.
    intros R ret H10 H11 Hra Hret. pose proof cs_bounds as (Bp & Bn & Bpn).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 (p + n)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 20%nat (@nil Z) (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    exists R'. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
    - eapply msteps_trans; [exact Hms|]. eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ].
    - rreg HR' 10%bv H10'. rewrite H10'. apply bv_eq. cbn [alu64 alu mul_div].
      rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      sub_mod_tac p n.
  Qed.

  Lemma from_algn : forall R q,
    p <= q <= p + n -> q mod 8 = 0 -> getr R 12%bv = Z_to_bv 64 q ->
    exists R', keptA R R' /\ msteps SEGS (st R SL_ALGN) (st R' SL_END) /\ getr R' 11%bv = Z_to_bv 64 (p + n).
  Proof using fx M p n HRO CS.
    intros R q Hq Hq8 H12. pose proof cs_bounds as (Bp & Bn & Bpn). pose proof (dn8_le (p + n)) as (D1 & D2 & D3).
    destruct (algn_block R q Hq Hq8 H12) as (R1 & K1 & MS1 & A12 & A11 & A13 & A14).
    pose proof (aligned_le_dn8 q (p + n) Hq8 ltac:(lia)) as HqD.
    assert (Hk : exists k : nat, q = dn8 (p + n) - 8 * Z.of_nat k).
    { exists (Z.to_nat ((dn8 (p + n) - q) / 8)).
      pose proof (Z.div_mod (dn8 (p + n) - q) 8 ltac:(lia)) as Hdm.
      assert (Hz : (dn8 (p + n) - q) mod 8 = 0).
      { rewrite Zminus_mod, D3, Hq8. reflexivity. }
      rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
    destruct Hk as [k Hk].
    destruct (word_loop k R1 q Hk ltac:(lia) Hq8 A12 A11 A13 A14) as (R2 & K2 & MS2 & B12 & B11).
    destruct (tail_loop (Z.to_nat (p + n - dn8 (p + n))) R2 (dn8 (p + n)) ltac:(lia) ltac:(lia) B12 B11) as (R3 & K3 & MS3 & C11).
    exists R3. split; [exact (keptA_trans _ _ _ K1 (keptA_trans _ _ _ K2 K3))|]. split; [|exact C11].
    eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2 | exact MS3].
  Qed.
End Strlen.

Theorem strlen_ro_spec : strlen_ro_stmt SEGS L tc.
Proof.
  intros fx R M ret HRO (p & n & CS & Ha0) Hra Hret.
  pose proof (cs_bounds p n CS) as (Bp & Bn & Bpn).
  assert (MAIN : exists R', msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_strlen tc)) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS))
                            /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 n).
  { change (tc_strlen tc) with SL_ENTRY.
    destruct (entry_block M p n HRO CS R Ha0) as (R1 & K1 & [(AL & MS1 & A12)|[(NAL & N0 & R'' & MS & K & A10)|(NAL & Npos & MS1 & A11 & A12)]]).
    - destruct (from_algn M p n HRO CS R1 p ltac:(lia) AL A12) as (R2 & K2 & MS2 & B11).
      destruct K1 as [K1 K1a]. destruct K2 as [K2 K2a].
      destruct (end_block M p n CS R2 ret ltac:(rewrite K2a, K1a; exact Ha0) B11
                  ltac:(rewrite <- Hra; symmetry; symmetry; apply (keeps_cs_trans _ _ _ K1 K2); (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret) as (R3 & K3 & MS3 & C10).
      exists R3. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2|exact MS3]|].
      split; [exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3) | exact C10].
    - exists R''. split.
      + eapply msteps_trans; [exact MS|]. eapply ret_run; [vm_compute; reflexivity | rewrite <- Hra; apply K; (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hret].
      + split; [exact K|]. rewrite A10, N0. reflexivity.
    - destruct (head_loop M p n HRO CS (Z.to_nat (n - 1)) R1 0 ltac:(lia) ltac:(lia) ltac:(rewrite A11; f_equal; lia) ltac:(rewrite A12; f_equal; lia))
        as (R2 & K2 & [(q & Hq8 & Hpq & MS2 & B12)|(MS2 & B11)]).
      + destruct (from_algn M p n HRO CS R2 q Hpq Hq8 B12) as (R3 & K3 & MS3 & C11).
        destruct K1 as [K1 K1a]. destruct K2 as [K2 K2a]. destruct K3 as [K3 K3a].
        destruct (end_block M p n CS R3 ret ltac:(rewrite K3a, K2a, K1a; exact Ha0) C11
                    ltac:(rewrite <- Hra; symmetry; symmetry; apply (keeps_cs_trans _ _ _ K1 (keeps_cs_trans _ _ _ K2 K3)); (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret) as (R4 & K4 & MS4 & D10).
        exists R4. split.
        * eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|exact MS4].
        * split; [exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 (keeps_cs_trans _ _ _ K2 K3)) K4) | exact D10].
      + destruct K1 as [K1 K1a]. destruct K2 as [K2 K2a].
        destruct (end_block M p n CS R2 ret ltac:(rewrite K2a, K1a; exact Ha0) B11
                    ltac:(rewrite <- Hra; symmetry; symmetry; apply (keeps_cs_trans _ _ _ K1 K2); (first [solve [clear; cbn; tauto] | cbn; tauto])) Hret) as (R3 & K3 & MS3 & C10).
        exists R3. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2|exact MS3]|].
        split; [exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3) | exact C10]. }
  destruct MAIN as (R' & MS & K & A10). exists R'. split; [exact MS|]. split; [exact K|].
  intros p' n' CS' Ha0'.

  pose proof (cs_bounds p' n' CS') as (Bp' & Bn' & Bpn').
  assert (Ep : p' = p).
  { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. rewrite !u64_of_Z in Ha0' by lia. lia. }
  subst p'.
  assert (En : n' = n).
  { destruct (Z.lt_total n' n) as [LT|[EQ|GT]]; [| exact EQ |].
    - exfalso. destruct (str_byte M p n HRO CS n' ltac:(lia)) as (c & Hc & Cc).
      pose proof (cell1_inj SEGS M _ _ _ Cc (nul_byte M p n' HRO CS')). lia.
    - exfalso. destruct (str_byte M p n' HRO CS' n ltac:(lia)) as (c & Hc & Cc).
      pose proof (cell1_inj SEGS M _ _ _ Cc (nul_byte M p n HRO CS)). lia. }
  subst n'. exact A10.
Qed.
