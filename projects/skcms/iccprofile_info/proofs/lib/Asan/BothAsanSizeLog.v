(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac RefMemcpyLib RefEnframeArith AgentLib
  Utf8Lib AsanUtf8Spec AsanUtf8Lib AsanNodesSL AsanNodesSLSoundCfg BothAsan_code_sl.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Section Smear.
  Variable m : Z.
  Hypothesis Hm : 0 <= m.

  (* [comment removed for export] *)
  Definition runs (r x : Z) : Prop :=
    0 <= x /\ (forall i, 0 <= i -> m - r < i <= m -> Z.testbit x i = true) /\ (forall i, m < i -> Z.testbit x i = false).

  Lemma runs_lt : forall r x, runs r x -> 0 <= x < 2 ^ (m + 1).
  Proof.
    intros r x (Hx & _ & Hhi). split; [lia|].
    apply Z_bounded_by_bits; [lia | lia |]. intros k Hk. apply Hhi. lia.
  Qed.

  Lemma runs_step : forall r s x, runs r x -> 0 < s <= r -> runs (r + s) (Z.lor x (Z.shiftr x s)).
  Proof.
    intros r s x (Hx & Hlo & Hhi) Hs. split; [apply Z.lor_nonneg; split; [lia | apply Z.shiftr_nonneg; lia]|]. split.
    - intros i Hi0 Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia.
      destruct (Z.lt_ge_cases (m - r) i) as [A|A].
      + rewrite (Hlo i) by lia. reflexivity.
      + rewrite (Hlo (i + s)) by lia. apply orb_true_r.
    - intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite (Hhi i), (Hhi (i + s)) by lia. reflexivity.
  Qed.

  Lemma runs_init : forall x, 2 ^ m <= x < 2 ^ (m + 1) -> runs 1 x.
  Proof.
    intros x Hx.
    assert (Hl : Z.log2 x = m).
    { pose proof (proj1 (Z.log2_le_pow2 x m ltac:(lia)) ltac:(lia)).
      pose proof (proj1 (Z.log2_lt_pow2 x (m + 1) ltac:(lia)) ltac:(lia)). lia. }
    split; [lia|]. split.
    - intros i Hi0 Hi. replace i with m by lia. rewrite <- Hl. apply Z.bit_log2. lia.
    - intros i Hi. apply Z.bits_above_log2; lia.
  Qed.

  Lemma runs_full : forall r x, runs r x -> m + 1 <= r -> x = 2 ^ (m + 1) - 1.
  Proof.
    intros r x (Hx & Hlo & Hhi) Hr. replace (2 ^ (m + 1) - 1) with (Z.ones (m + 1)) by (rewrite Z.ones_equiv; lia).
    apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec n (m + 1)); [apply Hlo; lia | apply Hhi; lia].
  Qed.

  (* [comment removed for export] *)
  Definition sm1 (x : Z) : Z := Z.lor x (Z.shiftr x 1).
  Definition sm2 (x : Z) : Z := Z.lor (sm1 x) (Z.shiftr (sm1 x) 2).
  Definition sm3 (x : Z) : Z := Z.lor (sm2 x) (Z.shiftr (sm2 x) 4).
  Definition sm4 (x : Z) : Z := Z.lor (sm3 x) (Z.shiftr (sm3 x) 8).
  Definition sm5 (x : Z) : Z := Z.lor (sm4 x) (Z.shiftr (sm4 x) 16).
  Definition sm6 (x : Z) : Z := Z.lor (sm5 x) (Z.shiftr (sm5 x) 32).

  Lemma smear_runs : forall x, 2 ^ m <= x < 2 ^ (m + 1) ->
    runs 2 (sm1 x) /\ runs 4 (sm2 x) /\ runs 8 (sm3 x) /\ runs 16 (sm4 x) /\ runs 32 (sm5 x) /\ runs 64 (sm6 x).
  Proof.
    intros x Hx. unfold sm6, sm5, sm4, sm3, sm2, sm1.
    pose proof (runs_init x Hx) as R1.
    pose proof (runs_step 1 1 _ R1 ltac:(lia)) as R2.
    pose proof (runs_step 2 2 _ R2 ltac:(lia)) as R3.
    pose proof (runs_step 4 4 _ R3 ltac:(lia)) as R4.
    pose proof (runs_step 8 8 _ R4 ltac:(lia)) as R5.
    pose proof (runs_step 16 16 _ R5 ltac:(lia)) as R6.
    pose proof (runs_step 32 32 _ R6 ltac:(lia)) as R7.
    exact (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 R7))))).
  Qed.

  Lemma smear6_eq : forall x, 2 ^ m <= x < 2 ^ (m + 1) -> m <= 63 -> sm6 x = 2 ^ (m + 1) - 1.
  Proof.
    intros x Hx Hm63. destruct (smear_runs x Hx) as (_ & _ & _ & _ & _ & R7). exact (runs_full 64 _ R7 ltac:(lia)).
  Qed.
End Smear.

Lemma shr_le : forall a s, 0 <= a -> 0 <= s -> 0 <= Z.shiftr a s <= a.
Proof.
  intros a s Ha Hs. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) Hs).
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma v_srli_Z : forall x s, 0 <= x < 2 ^ 64 -> 0 <= s -> v_srli (Z_to_bv 64 x) s = Z_to_bv 64 (Z.shiftr x s).
Proof. intros x s Hx Hs. unfold v_srli. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma v_sub_ZZ : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b Ha Hb. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sl_prod_shr : forall m, 0 <= m <= 63 -> Z.shiftr (SLN.sl_prod m) 56 = 63 - m.
Proof.
  intros m Hm.
  assert (exists k, m = Z.of_nat k /\ (k < 64)%nat) as [k [-> Hk]] by (exists (Z.to_nat m); lia).
  do 64 (destruct k as [|k]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.

Lemma sl_prod_range : forall m, 0 <= SLN.sl_prod m < 2 ^ 64.
Proof. intros m. unfold SLN.sl_prod. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SL.
  Variables (mem rom : word -> option byte) (x m c : Z) (bs : list byte) (w : word).
  Hypothesis Hm : 0 <= m <= 63.
  Hypothesis Hx : 2 ^ m <= x < 2 ^ (m + 1).
  Hypothesis Hx64 : x < 2 ^ 64.
  Hypothesis Hc : 0 <= c.
  Hypothesis Hc8 : c + 8 <= 2 ^ 64.
  Hypothesis Hbs : rdn ASEGS mem (Z_to_bv 64 c) 8 = Some bs.
  Hypothesis Hw : bytes_le_to_Z bs = bv_unsigned w.

  Let y : Z := 2 ^ 64 - 2 ^ (m + 1).
  Let y1 : Z := y - Z.land (Z.shiftr y 1) 0x5555555555555555.
  Let y2 : Z := Z.land y1 0x3333333333333333 + Z.land (Z.shiftr y1 2) 0x3333333333333333.
  Let y3 : Z := Z.land (y2 + Z.shiftr y2 4) 0x0F0F0F0F0F0F0F0F.

  Lemma y_facts :
    2 ^ (m + 1) <= 2 ^ 64 /\ 0 <= y < 2 ^ 64 /\ 0 <= y1 <= y /\ 0 <= Z.shiftr y 1 <= y /\ 0 <= Z.land (Z.shiftr y 1) 0x5555555555555555 <= Z.shiftr y 1
    /\ 0 <= Z.shiftr y1 2 <= y1 /\ 0 <= Z.land y1 0x3333333333333333 <= 0x3333333333333333
    /\ 0 <= Z.land (Z.shiftr y1 2) 0x3333333333333333 <= 0x3333333333333333
    /\ 0 <= y2 < 2 ^ 63 /\ 0 <= Z.shiftr y2 4 <= y2 /\ 0 <= y3 <= y2 + Z.shiftr y2 4.
  Proof.
    assert (P : 2 ^ (m + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    assert (P0 : 0 < 2 ^ (m + 1)) by (apply Z.pow_pos_nonneg; lia).
    assert (Y : 0 <= y < 2 ^ 64) by (subst y; lia).
    pose proof (shr_le y 1 ltac:(lia) ltac:(lia)) as S1.
    pose proof (land_range (Z.shiftr y 1) 0x5555555555555555 ltac:(lia) ltac:(lia)) as L1.
    assert (Y1 : 0 <= y1 <= y) by (subst y1; lia).
    pose proof (shr_le y1 2 ltac:(lia) ltac:(lia)) as S2.
    pose proof (land_range 0x3333333333333333 y1 ltac:(lia) ltac:(lia)) as L2. rewrite Z.land_comm in L2.
    pose proof (land_range 0x3333333333333333 (Z.shiftr y1 2) ltac:(lia) ltac:(lia)) as L3. rewrite Z.land_comm in L3.
    assert (Y2 : 0 <= y2 < 2 ^ 63) by (subst y2; lia).
    pose proof (shr_le y2 4 ltac:(lia) ltac:(lia)) as S3.
    pose proof (land_range (y2 + Z.shiftr y2 4) 0x0F0F0F0F0F0F0F0F ltac:(lia) ltac:(lia)) as L4.
    subst y3. repeat split; lia.
  Qed.

  Theorem sizelog_walk : forall regs,
    getr regs 18%bv = Z_to_bv 64 x -> v_addi (getr regs 9%bv) 48 = Z_to_bv 64 c ->
    exists regs',
      msteps ASEGS (mkst regs (0x35ea0 : word) mem rom) (mkst regs' (0x35f48 : word) mem rom)
      /\ getr regs' 19%bv = Z_to_bv 64 (63 - m)
      /\ getr regs' 11%bv = Z_to_bv 64 (SLN.sl_prod m)
      /\ getr regs' 12%bv = Z_to_bv 64 0x0101010101010101
      /\ getr regs' 14%bv = w
      /\ getr regs' 15%bv = Z_to_bv 64 0x0F0F0F0F0F0F0F0F
      /\ getr regs' 16%bv = Z_to_bv 64 0x01010101
      /\ (forall r, sl_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H18 H9c.
    pose proof y_facts as (P & Y & Y1 & S1 & L1 & S2 & L2 & L3 & Y2 & S3 & L4).
    destruct (smear_runs m ltac:(lia) x Hx) as (R2 & R3 & R4 & R5 & R6 & R7).
    apply (runs_lt m ltac:(lia)) in R2. apply (runs_lt m ltac:(lia)) in R3. apply (runs_lt m ltac:(lia)) in R4.
    apply (runs_lt m ltac:(lia)) in R5. apply (runs_lt m ltac:(lia)) in R6.
    pose proof (smear6_eq m ltac:(lia) x Hx ltac:(lia)) as SM.
    pose proof (shr_le x 1 ltac:(lia) ltac:(lia)). pose proof (shr_le (sm1 x) 2 ltac:(lia) ltac:(lia)).
    pose proof (shr_le (sm2 x) 4 ltac:(lia) ltac:(lia)). pose proof (shr_le (sm3 x) 8 ltac:(lia) ltac:(lia)).
    pose proof (shr_le (sm4 x) 16 ltac:(lia) ltac:(lia)). pose proof (shr_le (sm5 x) 32 ltac:(lia) ltac:(lia)).
    pose proof (sl_prod_range m) as PR. pose proof (sl_prod_shr m Hm) as SHR.
    eexists. split.
    - sn F_35ea0 D_35ea0; pin (Z.shiftr x 1) ltac:(rewrite v_srli_Z by lia; reflexivity).          (* [comment removed for export] *)
      sn F_35ea4 D_35ea4.                                                                        (* [comment removed for export] *)
      sn F_35ea8 D_35ea8.                                                                        (* [comment removed for export] *)
      sn F_35eac D_35eac.                                                                        (* [comment removed for export] *)
      sn F_35eb0 D_35eb0; pin (sm1 x) ltac:(unfold sm1; rewrite v_or_ZZ by lia; reflexivity).    (* [comment removed for export] *)
      sn F_35eb4 D_35eb4.                                                                        (* [comment removed for export] *)
      sn F_35eb8 D_35eb8.                                                                        (* [comment removed for export] *)
      sn F_35ebc D_35ebc.                                                                        (* [comment removed for export] *)
      sn F_35ec0 D_35ec0; pin (Z.shiftr (sm1 x) 2) ltac:(rewrite v_srli_Z by lia; reflexivity).  (* [comment removed for export] *)
      sn F_35ec4 D_35ec4; pin (sm2 x) ltac:(unfold sm2; rewrite v_or_ZZ by lia; reflexivity).    (* [comment removed for export] *)
      sn F_35ec8 D_35ec8.                                                                        (* [comment removed for export] *)
      sn F_35ecc D_35ecc.                                                                        (* [comment removed for export] *)
      sn F_35ed0 D_35ed0.                                                                        (* [comment removed for export] *)
      sn F_35ed4 D_35ed4.                                                                        (* [comment removed for export] *)
      sn F_35ed8 D_35ed8.                                                                        (* [comment removed for export] *)
      sn F_35edc D_35edc.                                                                        (* [comment removed for export] *)
      sn F_35ee0 D_35ee0; pin (Z.shiftr (sm2 x) 4) ltac:(rewrite v_srli_Z by lia; reflexivity).  (* [comment removed for export] *)
      sn F_35ee4 D_35ee4; pin (sm3 x) ltac:(unfold sm3; rewrite v_or_ZZ by lia; reflexivity).    (* [comment removed for export] *)
      sn F_35ee8 D_35ee8; pin (Z.shiftr (sm3 x) 8) ltac:(rewrite v_srli_Z by lia; reflexivity).  (* [comment removed for export] *)
      sn F_35eec D_35eec; pin (sm4 x) ltac:(unfold sm4; rewrite v_or_ZZ by lia; reflexivity).    (* [comment removed for export] *)
      sn F_35ef0 D_35ef0; pin (Z.shiftr (sm4 x) 16) ltac:(rewrite v_srli_Z by lia; reflexivity). (* [comment removed for export] *)
      sn F_35ef4 D_35ef4; pin (sm5 x) ltac:(unfold sm5; rewrite v_or_ZZ by lia; reflexivity).    (* [comment removed for export] *)
      sn F_35ef8 D_35ef8; pin (Z.shiftr (sm5 x) 32) ltac:(rewrite v_srli_Z by lia; reflexivity). (* [comment removed for export] *)
      sn F_35efc D_35efc; pin (2 ^ (m + 1) - 1) ltac:(rewrite v_or_ZZ by lia; rewrite <- SM; reflexivity).  (* [comment removed for export] *)
      sn F_35f00 D_35f00; pin y ltac:(rewrite v_not_lit by lia; subst y; f_equal; lia).           (* [comment removed for export] *)
      sn F_35f04 D_35f04; pin (Z.shiftr y 1) ltac:(rewrite v_srli_Z by lia; reflexivity).          (* [comment removed for export] *)
      sn F_35f08 D_35f08; pin (Z.land (Z.shiftr y 1) 0x5555555555555555) ltac:(rewrite v_and_ZZ by lia; reflexivity). (* [comment removed for export] *)
      sn F_35f0c D_35f0c.                                                                        (* [comment removed for export] *)
      sn F_35f10 D_35f10; pin y1 ltac:(rewrite v_sub_ZZ by lia; reflexivity).                     (* [comment removed for export] *)
      sn F_35f14 D_35f14; pin (Z.shiftr y1 2) ltac:(rewrite v_srli_Z by lia; reflexivity).         (* [comment removed for export] *)
      sn F_35f18 D_35f18; pin (Z.land y1 0x3333333333333333) ltac:(rewrite v_and_ZZ by lia; reflexivity).  (* [comment removed for export] *)
      sn F_35f1c D_35f1c; pin (Z.land (Z.shiftr y1 2) 0x3333333333333333) ltac:(rewrite v_and_ZZ by lia; reflexivity). (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (v := w);
          [exact F_35f20 | reflexivity | exact D_35f20 | gres; imm_norm; rewrite H9c; exact Hbs | exact Hw]
        | step_simpl]; vnorm.                                                                    (* [comment removed for export] *)
      sn F_35f24 D_35f24.                                                                        (* [comment removed for export] *)
      sn F_35f28 D_35f28; pin y2 ltac:(rewrite v_add_ZZ; reflexivity).                           (* [comment removed for export] *)
      sn F_35f2c D_35f2c; pin (Z.shiftr y2 4) ltac:(rewrite v_srli_Z by lia; reflexivity).         (* [comment removed for export] *)
      sn F_35f30 D_35f30; pin (y2 + Z.shiftr y2 4) ltac:(rewrite v_add_ZZ; reflexivity).          (* [comment removed for export] *)
      sn F_35f34 D_35f34.                                                                        (* [comment removed for export] *)
      sn F_35f38 D_35f38; pin y3 ltac:(rewrite v_and_ZZ by lia; reflexivity).                     (* [comment removed for export] *)
      sn F_35f3c D_35f3c.                                                                        (* [comment removed for export] *)
      sn F_35f40 D_35f40; pin (SLN.sl_prod m)
        ltac:(unfold v_mul; rewrite !u_Z2bv by lia; rewrite <- Z_to_bv64_mod; subst y y1 y2 y3; reflexivity).  (* [comment removed for export] *)
      sn F_35f44 D_35f44; pin (63 - m) ltac:(rewrite v_srli_Z by lia; rewrite SHR; reflexivity). (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; try (gres; reflexivity).
      intros r Hr. unfold sl_clob in Hr.
      repeat (apply orb_false_iff in Hr; destruct Hr as [Hr ?N]).
      repeat match goal with N : bv_eqb r ?k = false |- _ =>
        apply (f_equal negb) in N; cbn [negb] in N;
        let X := fresh in assert (X : r <> k) by (intros ->; unfold bv_eqb in N; rewrite Z.eqb_refl in N; discriminate N); clear N end.
      gres. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End SL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem asan_sizelog : sizelog_spec ASEGS SLN.SL_BOTH.
Proof.
  intros mem regs x m c bs w Hm Hx Hx64 H18 Hc Hc8 H9c Hbs Hw.
  destruct (sizelog_walk mem (seg_rom ASEGS) x m c bs w Hm Hx Hx64 Hbs Hw regs H18 H9c) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  cbn [SLN.sl_entry SLN.sl_exit SLN.SL_BOTH].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x35ea0) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x35f48) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.
End WithFP1.

