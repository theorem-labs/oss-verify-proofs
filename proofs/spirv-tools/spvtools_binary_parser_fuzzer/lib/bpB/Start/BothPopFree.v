(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSymExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BxSymExec3Sound.
From Stdlib Require Import FunctionalExtensionality.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition PW0 : bv 32 := 0x00465713.
Definition PW1 : bv 32 := 0xfff54793.
Definition PW2 : bv 32 := 0x00150513.
Definition PW3 : bv 32 := 0x00279793.
Definition PW4 : bv 32 := 0x00f587b3.
Definition PW5 : bv 32 := 0x00e7a023.
Definition PW6 : bv 32 := 0x01560633.
Definition PW7 : bv 32 := 0xff3562e3.

Lemma PD0 : decode_any PW0 = Some (ShiftImm ALU_SRL 14 12 4, 4%Z). Proof. vm_refl. Qed.
Lemma PD1 : decode_any PW1 = Some (OpImm ALU_XOR 15 10 4095, 4%Z). Proof. vm_refl. Qed.
Lemma PD2 : decode_any PW2 = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. vm_refl. Qed.
Lemma PD3 : decode_any PW3 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z). Proof. vm_refl. Qed.
Lemma PD4 : decode_any PW4 = Some (Op ALU_ADD 15 11 15, 4%Z). Proof. vm_refl. Qed.
Lemma PD5 : decode_any PW5 = Some (Store SZ4 15 14 0, 4%Z). Proof. vm_refl. Qed.
Lemma PD6 : decode_any PW6 = Some (Op ALU_ADD 12 12 21, 4%Z). Proof. vm_refl. Qed.
Lemma PD7 : decode_any PW7 = Some (Branch BC_LTU 10 19 8164, 4%Z). Proof. vm_refl. Qed.

Fixpoint pf_mem (mem : word -> option byte) (e c s i : Z) (k : nat) : word -> option byte :=
  match k with
  | O => mem
  | S k' => pf_mem (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16))))
                   e (c + s) s (i + 1) k'
  end.

Fixpoint pf_bytes (c s : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => Z_to_le_bytes 4 ((c + Z.of_nat k' * s) / 16) ++ pf_bytes c s k'
  end.

Lemma pf_bytes_length : forall c s k, length (pf_bytes c s k) = (4 * k)%nat.
Proof. intros c s k. induction k as [|k IH]; cbn [pf_bytes length]; [reflexivity|]. rewrite length_app, length_Z_to_le_bytes, IH. lia. Qed.

Lemma pf_bytes_nth : forall c s k j t,
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  nth (Z.to_nat (4 * j) + t) (pf_bytes c s k) (Z_to_bv 8 0) = nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0).
Proof.
  intros c s k. induction k as [|k IH]; intros j t Hj Ht; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - rewrite app_nth1 by (rewrite length_Z_to_le_bytes; lia). replace (Z.to_nat (4 * 0) + t)%nat with t by lia. f_equal. f_equal. f_equal. lia.
  - rewrite app_nth2 by (rewrite length_Z_to_le_bytes; lia). rewrite length_Z_to_le_bytes.
    replace (Z.to_nat (4 * j) + t - 4)%nat with (Z.to_nat (4 * (j - 1)) + t)%nat by lia.
    rewrite IH by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma pf_bytes_cell : forall c s k j,
  (0 <= j < Z.of_nat k)%Z ->
  firstn 4 (skipn (Z.to_nat (4 * j)) (pf_bytes c s k)) = Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16).
Proof.
  intros c s k. induction k as [|k IH]; intros j Hj; [lia|].
  cbn [pf_bytes]. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eq_dec j 0) as [->|Hj0].
  - replace (Z.to_nat (4 * 0)) with 0%nat by lia. rewrite skipn_O. rewrite firstn_app, length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_Z_to_le_bytes; lia). f_equal. f_equal. lia.
  - rewrite skipn_app, length_Z_to_le_bytes. rewrite skipn_all2 by (rewrite length_Z_to_le_bytes; lia). cbn [app].
    replace (Z.to_nat (4 * j) - 4)%nat with (Z.to_nat (4 * (j - 1)))%nat by lia.
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Definition popfree_spec (SEGS : list Segment) (p : Z) : Prop :=
  forall regs mem (i e c s n : Z),
    getr regs 10%bv = Z_to_bv 64 i -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 c ->
    getr regs 21%bv = Z_to_bv 64 s -> getr regs 19%bv = Z_to_bv 64 n ->
    (0 <= i < n)%Z -> (4 * n <= e < 2 ^ 64)%Z -> (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
    store_ok SEGS mem (Z_to_bv 64 (e - 4 * n)) (Z.to_nat (4 * (n - i))) = true ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 p) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 (p + 32)) (wbytes mem (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) (seg_rom SEGS))
      /\ getr regs' 10%bv = Z_to_bv 64 n /\ getr regs' 12%bv = Z_to_bv 64 (c + (n - i) * s)
      /\ getr regs' 14%bv = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15%bv = Z_to_bv 64 (e - 4 * n)
      /\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).

Section PopFreeLoop.
Variable segs : list Segment.
Variable p : Z.
Hypothesis Hp : (28 <= p)%Z /\ (p + 32 < 2 ^ 64)%Z.
Hypothesis HF0 : fetch_word segs (Z_to_bv 64 p) = Some PW0.
Hypothesis HF1 : fetch_word segs (Z_to_bv 64 (p + 4)) = Some PW1.
Hypothesis HF2 : fetch_word segs (Z_to_bv 64 (p + 8)) = Some PW2.
Hypothesis HF3 : fetch_word segs (Z_to_bv 64 (p + 12)) = Some PW3.
Hypothesis HF4 : fetch_word segs (Z_to_bv 64 (p + 16)) = Some PW4.
Hypothesis HF5 : fetch_word segs (Z_to_bv 64 (p + 20)) = Some PW5.
Hypothesis HF6 : fetch_word segs (Z_to_bv 64 (p + 24)) = Some PW6.
Hypothesis HF7 : fetch_word segs (Z_to_bv 64 (p + 28)) = Some PW7.

Definition iter_regs (regs : bvmap 5 word) (i e c s : Z) : bvmap 5 word :=
  regupd (regupd (regupd (regupd regs 14 (Z_to_bv 64 (c / 16))) 10 (Z_to_bv 64 (i + 1)))
                 15 (Z_to_bv 64 (e - 4 * (i + 1)))) 12 (Z_to_bv 64 (c + s)).

Ltac red_if :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      let v := eval vm_compute in (bv_eqb a b) in
      lazymatch v with
      | true => change (if bv_eqb a b then x else y) with x
      | false => change (if bv_eqb a b then x else y) with y
      end
  end.

Lemma u64_of_Z : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Ltac gr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

Lemma pf_iter : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i + 1 <= n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + s < 2 ^ 64)%Z ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (i + 1))) 4 = true ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (if (i + 1 <? n)%Z then p else p + 32))
                      (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom)
    /\ getr regs' 10 = Z_to_bv 64 (i + 1) /\ getr regs' 11 = Z_to_bv 64 e /\ getr regs' 12 = Z_to_bv 64 (c + s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 (c / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * (i + 1))
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hok.
  destruct Hp as [Hp0 Hp1].

  assert (V14 : v_srli (Z_to_bv 64 c) (bv_unsigned (4 : bv 6)) = Z_to_bv 64 (c / 16)).
  { unfold v_srli. rewrite u64_of_Z by lia. change (bv_unsigned (4 : bv 6)) with 4%Z.
    rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (V15a : v_xori (Z_to_bv 64 i) (bv_signed (4095 : bv 12)) = Z_to_bv 64 (2 ^ 64 - 1 - i)).
  { unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (bv_signed (4095 : bv 12))) with (2 ^ 64 - 1)%Z.
    rewrite AX2S.lxor_ones64 by lia. reflexivity. }
  assert (V10 : v_addi (Z_to_bv 64 i) (bv_signed (1 : bv 12)) = Z_to_bv 64 (i + 1)).
  { change (bv_signed (1 : bv 12)) with 1%Z. apply v_addi_lit. }
  assert (V15b : v_slli (Z_to_bv 64 (2 ^ 64 - 1 - i)) (bv_unsigned (2 : bv 6)) = Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)).
  { unfold v_slli. rewrite u64_of_Z by lia. change (bv_unsigned (2 : bv 6)) with 2%Z.
    rewrite Z.shiftl_mul_pow2 by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal. lia. }
  assert (V15c : v_add (Z_to_bv 64 e) (Z_to_bv 64 (2 ^ 66 - 4 - 4 * i)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { unfold v_add. rewrite u64_of_Z by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    rewrite Z.add_mod_idemp_r by lia.
    replace (e + (2 ^ 66 - 4 - 4 * i))%Z with ((e - 4 * (i + 1)) + 4 * 2 ^ 64)%Z by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Vst : v_addi (Z_to_bv 64 (e - 4 * (i + 1))) (bv_signed (0 : bv 12)) = Z_to_bv 64 (e - 4 * (i + 1))).
  { change (bv_signed (0 : bv 12)) with 0%Z. rewrite v_addi_lit. f_equal. lia. }
  assert (V12 : v_add (Z_to_bv 64 c) (Z_to_bv 64 s) = Z_to_bv 64 (c + s)).
  { unfold v_add. rewrite !u64_of_Z by lia. reflexivity. }
  eexists. split.
  - eapply mst_step; [reflexivity | eapply (step_srli segs); [exact HF0 | reflexivity | exact PD0] |].
    red_if. rewrite v_addi_lit, H12, V14.
    eapply mst_step; [reflexivity | eapply (step_xori segs); [exact HF1 | reflexivity | exact PD1] |].
    red_if. rewrite v_addi_lit. replace (p + 4 + 4)%Z with (p + 8)%Z by lia. gr. rewrite H10, V15a.
    eapply mst_step; [reflexivity | eapply (step_addi segs); [exact HF2 | reflexivity | exact PD2] |].
    red_if. rewrite v_addi_lit. replace (p + 8 + 4)%Z with (p + 12)%Z by lia. gr. rewrite H10, V10.
    eapply mst_step; [reflexivity | eapply (step_slli segs); [exact HF3 | reflexivity | exact PD3] |].
    red_if. rewrite v_addi_lit. replace (p + 12 + 4)%Z with (p + 16)%Z by lia. gr. rewrite V15b.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF4 | reflexivity | exact PD4] |].
    red_if. rewrite v_addi_lit. replace (p + 16 + 4)%Z with (p + 20)%Z by lia. gr. rewrite H11, V15c.
    eapply mst_step; [reflexivity | eapply (step_sw_val segs); [exact HF5 | reflexivity | exact PD5 | gr; rewrite Vst; exact Hok] |].
    rewrite v_addi_lit. replace (p + 20 + 4)%Z with (p + 24)%Z by lia. gr. rewrite Vst.
    eapply mst_step; [reflexivity | eapply (step_add segs); [exact HF6 | reflexivity | exact PD6] |].
    red_if. rewrite v_addi_lit. replace (p + 24 + 4)%Z with (p + 28)%Z by lia. gr. rewrite H12, H21, V12.
    destruct (Z.ltb (i + 1) n) eqn:Hlt.
    + eapply mst_step; [reflexivity | eapply (step_bltu_tk segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite btgt_lit. change (bv_signed (8164 : bv 13)) with (-28)%Z.
      replace (p + 28 + -28)%Z with p by lia. apply mst_refl.
    + eapply mst_step; [reflexivity | eapply (step_bltu_ft segs); [exact HF7 | reflexivity | exact PD7 | ] |].
      { gr. rewrite H19. unfold c_ltu, bv_ltu. rewrite !u64_of_Z by lia. exact Hlt. }
      rewrite v_addi_lit. replace (p + 28 + 4)%Z with (p + 32)%Z by lia. apply mst_refl.
  - gr. rewrite H11, H21, H19.
    repeat (split; [reflexivity|]).
    intros r Hr10 Hr12 Hr14 Hr15. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma pf_loop : forall k regs mem rom i e c s n,
  n = (i + Z.of_nat (S k))%Z ->
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + Z.of_nat (S k) * s < 2 ^ 64)%Z ->
  (forall j, (i <= j < n)%Z -> RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * (j + 1))) 4 = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (S k)) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + Z.of_nat (S k) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + Z.of_nat k * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  induction k as [|k IH]; intros regs mem rom i e c s n Hn H10 H11 H12 H21 H19 Hi Hne He Hc Hs Hcs Hok.
  -
    change (Z.of_nat 1) with 1%Z in *. change (Z.of_nat 0) with 0%Z. rewrite Z.mul_1_l in *. rewrite Z.mul_0_l, Z.add_0_r.
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    exists regs'. destruct (Z.ltb_spec (i + 1) n); [lia|].
    cbn [pf_mem].
    split; [exact Hms|]. rewrite R10, R11, R12, R21, R19, R14, R15. subst n.
    repeat (split; [reflexivity|]). exact Rothers.
  -
    rewrite Nat2Z.inj_succ in Hn, Hcs |- *. rewrite Nat2Z.inj_succ in Hcs |- *.
    assert (Hks : (0 <= Z.of_nat k * s)%Z) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hs1 : (c + s < 2 ^ 64)%Z) by lia.
    destruct (pf_iter regs mem rom i e c s n H10 H11 H12 H21 H19 Hi ltac:(lia) Hne He Hc Hs Hs1
                (Hok i ltac:(lia))) as (regs1 & Hms1 & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Rothers).
    destruct (Z.ltb_spec (i + 1) n); [|lia].
    destruct (IH regs1 (wbytes mem (Z_to_bv 64 (e - 4 * (i + 1))) (word_to_le_bytes 4 (Z_to_bv 64 (c / 16)))) rom
                 (i + 1)%Z e (c + s)%Z s n ltac:(rewrite Nat2Z.inj_succ; lia) R10 R11 R12 R21 R19 ltac:(lia) Hne He ltac:(lia) Hs
                 ltac:(rewrite Nat2Z.inj_succ; lia))
      as (regs2 & Hms2 & S10 & S11 & S12 & S21 & S19 & S14 & S15 & Sothers).
    { intros j Hj. eapply store_ok_mono; [apply wbytes_grows | apply Hok; lia]. }
    exists regs2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    rewrite S10, S11, S12, S21, S19, S14, S15.
    split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; f_equal; lia|]. split; [reflexivity|].
    intros r A B C D. rewrite (Sothers r A B C D). apply Rothers; assumption.
Qed.

Lemma pf_wbytes_inside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma pf_wbytes_outside : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

Lemma pf_mem_frame : forall k mem e c s i (a : word),
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (bv_unsigned a < e - 4 * (i + Z.of_nat k) \/ e - 4 * i <= bv_unsigned a)%Z ->
  pf_mem mem e c s i k a = mem a.
Proof.
  induction k as [|k IH]; intros mem e c s i a Hi Hk He Ha; [reflexivity|].
  cbn [pf_mem]. rewrite IH by lia.
  apply pf_wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; cbn [Z.of_nat]; lia.
Qed.

Lemma word_to_le_bytes4_Z : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. apply Z_to_le_bytes_wrap. cbn; lia. Qed.

Lemma pf_mem_cell : forall k mem e c s i j t,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= j < Z.of_nat k)%Z -> (t < 4)%nat ->
  pf_mem mem e c s i k (Z_to_bv 64 (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t))
  = Some (nth t (Z_to_le_bytes 4 ((c + (Z.of_nat k - 1 - j) * s) / 16)) (Z_to_bv 8 0)).
Proof.
  induction k as [|k IH]; intros mem e c s i j t Hi Hk He Hj Ht; [lia|].
  rewrite Nat2Z.inj_succ in *.
  cbn [pf_mem].
  destruct (Z.eq_dec j (Z.of_nat k)) as [->|Hne].
  -
    rewrite pf_mem_frame; [| lia | lia | lia | rewrite u64_of_Z by lia; lia].
    rewrite pf_wbytes_inside; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; [| cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia].
    rewrite word_to_le_bytes4_Z. f_equal. f_equal; [lia|]. f_equal. f_equal. lia.
  - replace (e - 4 * (i + Z.succ (Z.of_nat k)) + 4 * j + Z.of_nat t)%Z
      with (e - 4 * ((i + 1) + Z.of_nat k) + 4 * j + Z.of_nat t)%Z by lia.
    rewrite (IH _ e (c + s)%Z s (i + 1)%Z j t) by lia.
    f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Theorem popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok segs mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps segs (mkst regs (Z_to_bv 64 p) mem rom)
                (mkst regs' (Z_to_bv 64 (p + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom i e c s n H10 H11 H12 H21 H19 Hi Hin Hne He Hc Hs Hcs Hwr.
  destruct (Z.to_nat (n - i)) as [|k] eqn:Hk; [lia|].
  assert (Hkz : (Z.of_nat (S k) = n - i)%Z) by lia.
  destruct (pf_loop k regs mem rom i e c s n ltac:(lia) H10 H11 H12 H21 H19 Hi Hne He Hc Hs ltac:(rewrite Hkz; exact Hcs))
    as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros j Hj. replace (e - 4 * (j + 1))%Z with (e - 4 * n + 4 * (n - j - 1))%Z by lia. apply Hwr; lia. }
  exists regs'. rewrite R10, R11, R12, R21, R19, R14, R15, Hkz.
  replace (Z.of_nat k) with (n - i - 1)%Z by lia.
  repeat (split; [first [exact Hms | reflexivity]|]). exact Ro.
Qed.

Lemma pf_mem_wbytes : forall k mem e c s i,
  (0 <= i)%Z -> (4 * (i + Z.of_nat k) <= e)%Z -> (e < 2 ^ 64)%Z ->
  pf_mem mem e c s i k = wbytes mem (Z_to_bv 64 (e - 4 * (i + Z.of_nat k))) (pf_bytes c s k).
Proof.
  intros k mem e c s i Hi Hk He. apply functional_extensionality. intros a.
  pose proof (u64_range a) as Ra. pose proof (pf_bytes_length c s k) as L.
  destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * (i + Z.of_nat k))) as [Hlt|Hge];
    [|destruct (Z_lt_le_dec (bv_unsigned a) (e - 4 * i)) as [Hlt2|Hge2]].
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
  - set (base := (e - 4 * (i + Z.of_nat k))%Z) in *.
    set (j := ((bv_unsigned a - base) / 4)%Z). set (t := Z.to_nat ((bv_unsigned a - base) mod 4)).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hj : (0 <= j < Z.of_nat k)%Z) by (subst j base; lia).
    assert (Ht : (t < 4)%nat) by (subst t; lia).
    assert (Ha : a = Z_to_bv 64 (base + 4 * j + Z.of_nat t)).
    { apply bv_eq. rewrite u64_of_Z by (subst j t base; lia). subst j t base. lia. }
    rewrite Ha. subst base. rewrite (pf_mem_cell k mem e c s i j t Hi Hk He Hj Ht).
    rewrite pf_wbytes_inside; rewrite ?L, ?u64_of_Z by lia; [|lia|lia].
    replace (Z.to_nat (e - 4 * (i + Z.of_nat k) + 4 * j + Z.of_nat t - (e - 4 * (i + Z.of_nat k)))) with (Z.to_nat (4 * j) + t)%nat by lia.
    symmetry. f_equal. apply pf_bytes_nth; assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - rewrite pf_mem_frame by lia. symmetry. apply pf_wbytes_outside; rewrite L, u64_of_Z by lia; lia.
Qed.

Theorem popfree_spec_of_code : popfree_spec segs p.
Proof.
  intros regs mem i e c s n H10 H11 H12 H21 H19 Hin He Hc Hs Hcs Hok.
  destruct (popfree_loop_run regs mem (seg_rom segs) i e c s n H10 H11 H12 H21 H19
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hc Hs Hcs) as (regs' & Hms & R10 & R11 & R12 & R21 & R19 & R14 & R15 & Ro).
  { intros d m Hd Hdm. eapply (store_ok_sub segs mem _ _ (Z.to_nat (4 * (n - i))) m); [| exact Hok | |]; rewrite !u64_of_Z by lia; lia. }
  exists regs'. rewrite (pf_mem_wbytes (Z.to_nat (n - i)) mem e c s i) in Hms by lia.
  replace (i + Z.of_nat (Z.to_nat (n - i)))%Z with n in Hms by lia.
  split; [exact Hms|]. split; [exact R10|]. split; [exact R12|]. split; [exact R14|]. split; [exact R15|]. exact Ro.
Qed.

End PopFreeLoop.
