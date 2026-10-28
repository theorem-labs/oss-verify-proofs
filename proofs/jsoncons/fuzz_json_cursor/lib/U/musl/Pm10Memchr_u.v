(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.musl Require Import Pm10MemcpyBase_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10_code_b5000_b6000_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Definition Mc : Z := 0x0101010101010100.
Definition Hc : Z := 0x8080808080808080.

Definition LDv (l : list byte) : word := Z_to_bv 64 (bytes_le_to_Z l).

Lemma u_LDv : forall l, length l = 8%nat -> bv_unsigned (LDv l) = bytes_le_to_Z l.
Proof. intros l H. unfold LDv. pose proof (bytes_le_to_Z_range l H). apply u_Z2bv; lia. Qed.

Definition TW (x : word) : word :=
  v_and (v_or (v_sub (Z_to_bv 64 Mc) (v_xor x (Z_to_bv 64 0))) (v_xor x (Z_to_bv 64 0))) (Z_to_bv 64 Hc).

Lemma v_xor_0 : forall x : word, v_xor x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_xor. rewrite (u_Z2bv 0) by lia. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma TW_bits : forall x : word, let y := bv_unsigned x in
  (forall i, (0 <= i)%Z ->
     Z.testbit (bv_unsigned (TW x)) i = (Z.testbit Hc i && negb (Z.testbit (HZ.Tz y) i))%bool)
  /\ (forall i, (0 <= i)%Z -> Z.testbit (HZ.Tz y) i = true -> Z.testbit Hc i = true).
Proof.
  intros x y. pose proof (u64_range x) as Hx. subst y.
  assert (A64 : (0 <= (bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  set (A := ((bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64)%Z) in *.

  assert (SUB : ((Mc - bv_unsigned x) mod 2 ^ 64 = 2 ^ 64 - 1 - A)%Z).
  { subst A. unfold Mc, HZ.ONESNEG.
    rewrite <- (Z.mod_add _ 1) by lia.
    replace (72340172838076672 - bv_unsigned x + 1 * 2 ^ 64)%Z
      with (2 ^ 64 - 1 - (bv_unsigned x + 18374403900871474943) + 1 * 2 ^ 64)%Z by lia.
    set (z := (bv_unsigned x + 18374403900871474943)%Z).
    rewrite Zminus_mod_idemp_r || idtac.
    pose proof (Z.div_mod z (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
    set (q := (z / 2 ^ 64)%Z) in *. set (r := (z mod 2 ^ 64)%Z) in *.
    replace (2 ^ 64 - 1 - z + 1 * 2 ^ 64)%Z with ((2 ^ 64 - 1 - r) + (1 - q) * 2 ^ 64)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (NOTA : forall i, (0 <= i < 64)%Z -> Z.testbit (2 ^ 64 - 1 - A) i = negb (Z.testbit A i)).
  { intros i Hi. replace (2 ^ 64 - 1 - A)%Z with ((Z.lnot A) mod 2 ^ 64)%Z.
    - rewrite Z.mod_pow2_bits_low by lia. apply Z.lnot_spec. lia.
    - unfold Z.lnot. replace (Z.pred (- A)) with ((2 ^ 64 - 1 - A) + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (TWu : bv_unsigned (TW x) = Z.land (Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x)) Hc).
  { unfold TW. rewrite !v_xor_0. unfold v_and, v_or, v_sub.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small Mc) by (unfold Mc; lia). rewrite (Z.mod_small Hc) by (unfold Hc; lia).
    assert (R1 : (0 <= (Mc - bv_unsigned x) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
    assert (R2 : (0 <= Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x) < 2 ^ 64)%Z) by (apply Z_lor_range; lia).
    rewrite (Z.mod_small (Z.lor _ _)) by exact R2.
    apply Z.mod_small. apply Z_land_range; [exact R2 | unfold Hc; lia]. }
  split.
  - intros i Hi. rewrite TWu, SUB.
    unfold HZ.Tz. fold A.
    rewrite Z.land_spec. rewrite Z.lor_spec. rewrite Z.land_spec. rewrite Z.land_spec. rewrite Z.lxor_spec.
    change HZ.HIGHS with Hc.
    destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
    + rewrite NOTA by lia.
      replace (Z.testbit HZ.ALLONES i) with true.
      2:{ symmetry. unfold HZ.ALLONES. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.ones_spec_low; [reflexivity|lia]. }
      destruct (Z.testbit A i), (Z.testbit (bv_unsigned x) i), (Z.testbit Hc i); reflexivity.
    + replace (Z.testbit Hc i) with false.
      2:{ symmetry. apply (Z_testbit_high 64); unfold Hc; lia. }
      rewrite andb_false_r. reflexivity.
  - intros i Hi H. unfold HZ.Tz in H. rewrite Z.land_spec in H. rewrite Z.land_spec in H.
    change HZ.HIGHS with Hc in H.
    destruct (Z.testbit Hc i); [reflexivity|]. rewrite andb_false_r in H. discriminate H.
Qed.

Lemma TW_eq_H : forall x : word, c_eq (TW x) (Z_to_bv 64 Hc) = Z.eqb (HZ.Tz (bv_unsigned x)) 0.
Proof.
  intros x. destruct (TW_bits x) as [B1 B2].
  unfold c_eq, bv_eqb. rewrite (u_Z2bv Hc) by (unfold Hc; lia).
  pose proof (HZ.Tz_range (bv_unsigned x)) as TR.
  destruct (Z.eqb_spec (HZ.Tz (bv_unsigned x)) 0) as [Z0|NZ].
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite B1 by lia. rewrite Z0, Z.bits_0.
    rewrite andb_true_r. reflexivity.
  - apply Z.eqb_neq. intros E.
    apply NZ. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z.testbit (HZ.Tz (bv_unsigned x)) i) eqn:T; [|reflexivity].
    pose proof (B2 i Hi T) as HH.
    pose proof (B1 i Hi) as BB. rewrite E, HH, T in BB. discriminate BB.
Qed.

Lemma TW_nozero : forall l, length l = 8%nat ->
  (forall i, (i < 8)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) <> 0%Z) ->
  c_eq (TW (LDv l)) (Z_to_bv 64 Hc) = true.
Proof.
  intros l Hl Hnz. rewrite TW_eq_H. apply Z.eqb_eq.
  rewrite u_LDv by exact Hl. apply HZ.Tz_nozero.
  - apply bytes_le_to_Z_range. exact Hl.
  - intros i Hi. rewrite zb_of_bytes by (rewrite Hl; exact Hi). apply Hnz. exact Hi.
Qed.

Lemma TW_haszero : forall l (i : nat), length l = 8%nat -> (i < 8)%nat ->
  bv_unsigned (nth i l (Z_to_bv 8 0)) = 0%Z ->
  (forall j, (j < i)%nat -> bv_unsigned (nth j l (Z_to_bv 8 0)) <> 0%Z) ->
  c_eq (TW (LDv l)) (Z_to_bv 64 Hc) = false.
Proof.
  intros l i Hl Hi Hz Hnz. rewrite TW_eq_H. apply Z.eqb_neq.
  rewrite u_LDv by exact Hl. apply (HZ.Tz_haszero _ i).
  - apply bytes_le_to_Z_range. exact Hl.
  - exact Hi.
  - rewrite zb_of_bytes by (rewrite Hl; exact Hi). exact Hz.
  - intros j Hj. rewrite zb_of_bytes by (rewrite Hl; lia). apply Hnz. exact Hj.
Qed.

Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x147d0 <= i < 0x147e8)%Z -> mem (Z_to_bv 64 i) = None.

Lemma rd_const_M : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x147e0) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Mc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 83936)) with 83936%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 83936)) with 83936%Z in Hx. cbn in Hx. lia.
Qed.

Lemma rd_const_H : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x147d0) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Hc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 83920)) with 83920%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 83920)) with 83920%Z in Hx. cbn in Hx. lia.
Qed.

Lemma nth_sub : forall (bs : list byte) j m i d,
  (i < m)%nat -> (j + m <= length bs)%nat -> nth i (sub bs j m) d = nth (j + i) bs d.
Proof.
  intros bs j m i d Hi Hjm. unfold sub.
  rewrite nth_firstn. replace (i <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn. reflexivity.
Qed.

Lemma c_eq_LBv_0 : forall b : byte, c_eq (LBv b) (Z_to_bv 64 0) = (bv_unsigned b =? 0)%Z.
Proof.
  intros b. unfold c_eq, bv_eqb, LBv. pose proof (bv_unsigned_in_range _ b) as R.
  change (bv_modulus 8) with 256%Z in R.
  rewrite (u_Z2bv (bv_unsigned b)) by lia. rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {

  Hbuf : rdn RSEGS mem s (length buf) = Some buf;

  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;

  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;

  HKn  : (K + 8 <= n)%Z;
  Hn64 : (n < 2 ^ 64)%Z;
  Hro  : rodata_clear mem }.

Section MCHR.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.

  #[local] Notation L := (Z.of_nat (length buf)).
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ _ HOK.
  Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ _ HOK.
  Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ _ HOK.
  Let HKn : (K + 8 <= n)%Z := HKn _ _ _ _ _ HOK.
  Let Hn64 : (n < 2 ^ 64)%Z := Hn64 _ _ _ _ _ HOK.
  Let Hro := Hro _ _ _ _ _ HOK.

  Lemma KL : (K + 1 <= L)%Z.
  Proof.
    clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
  Qed.

  Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
  Lemma KE_facts : (K + 1 <= KE <= K + 8)%Z /\ (KE <= L)%Z /\ ((bv_unsigned s + KE) mod 8 = 0)%Z.
  Proof.
    unfold KE. clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    repeat split; try lia.
    replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
      with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma bz : bv_unsigned (b_ K) = 0%Z.
  Proof. exact (Hzero _ _ _ _ _ HOK). Qed.
  Lemma bnz : forall j, (0 <= j < K)%Z -> bv_unsigned (b_ j) <> 0%Z.
  Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ _ HOK). lia. Qed.

  Lemma rd_w : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z ->
    rdn RSEGS mem (at_ s j) m = Some (sb_ j m).
  Proof.
    intros j m Hj Hm. unfold sb_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
  Qed.

  Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z ->
    rdn RSEGS mem (at_ s j) 1 = Some [b_ j].
  Proof.
    intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.

  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.

  Lemma sb_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= L)%Z ->
    nth i (sb_ j 8) (Z_to_bv 8 0) = b_ (j + Z.of_nat i).
  Proof.
    intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
  Qed.

  Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.

  Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.

  Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  Lemma tw_hit : forall j, (0 <= j <= K)%Z -> (K < j + 8)%Z -> (j + 8 <= L)%Z ->
    c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = false.
  Proof.
    intros j Hj HKj HL.
    apply (TW_haszero _ (Z.to_nat (K - j))).
    - apply sb_len; lia.
    - lia.
    - rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
    - intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Lemma tw_miss : forall j, (0 <= j)%Z -> (j + 8 <= K)%Z -> (j + 8 <= L)%Z ->
    c_eq (TW (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = true.
  Proof.
    intros j Hj HKj HL. apply TW_nozero.
    - apply sb_len; lia.
    - intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.

  Ltac condb :=
    rwH; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].

  Ltac cond := try unfold v_addi; cond_lia.

  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ (v_xor ?x _)) _) _) _ = ?b =>
      change (c_eq (TW x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; unorm; f_equal; lia); try solve_keeps_cs.

  Lemma t_found : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s K -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0xb7838 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11. pose proof KL. eexists. split.
    - mlbu F_b59a8 D_b59a8 K.
      stepb_tk F_b59ac D_b59ac ltac:(condb).
      stepret F_b59c0 D_b59c0 ret ltac:(exact H1).
      apply mst_refl.
    - post.
  Qed.

  Lemma t_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 13 = Z_to_bv 64 m ->
    (0 <= j < K)%Z -> (Z.of_nat i = K - 1 - j)%Z -> (K - j + 1 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb7840 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H13 Hj Hi Hm.
    -
      eexists. split.
      + stepn F_b59b0 D_b59b0.
        stepn F_b59b4 D_b59b4.
        stepb_tk F_b59b8 D_b59b8 ltac:(cond).
        mlbu F_b59a8 D_b59a8 K.
        stepb_tk F_b59ac D_b59ac ltac:(condb).
        stepret F_b59c0 D_b59c0 ret ltac:(exact H1).
        apply mst_refl.
      + post.
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7840 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 13 = Z_to_bv 64 (m - 1) /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_b59b0 D_b59b0.
          stepn F_b59b4 D_b59b4.
          stepb_tk F_b59b8 D_b59b8 ltac:(cond).
          mlbu F_b59a8 D_b59a8 (j + 1)%Z.
          stepb_ft F_b59ac D_b59ac ltac:(condb).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
        destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  Lemma w_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 7 ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb780c : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3).
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H13 H14 H15 H16 Hj Hal Hi Hm;
      pose proof (al_room j Hal Hj) as HR.
    -
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      destruct (Z.eq_dec j K) as [HjK|HjK].
      +
        eexists. split.
        * mld F_b597c D_b597c j.
          stepn F_b5980 D_b5980.
          stepn F_b5984 D_b5984.
          stepn F_b5988 D_b5988.
          stepn F_b598c D_b598c.
          stepb_tk F_b5990 D_b5990 ltac:(condw tw_hit).
          stepn F_b59c4 D_b59c4.
          mlbu F_b59c8 D_b59c8 j.
          stepb_ft F_b59cc D_b59cc ltac:(condb).
          stepn F_b59d0 D_b59d0.
          stepret F_b59c0 D_b59c0 ret ltac:(exact H1).
          apply mst_refl.
        * post.
      +
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7840 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 13 = Z_to_bv 64 m /\ keeps_cs regs r)).
        * eexists. split.
          -- mld F_b597c D_b597c j.
             stepn F_b5980 D_b5980.
             stepn F_b5984 D_b5984.
             stepn F_b5988 D_b5988.
             stepn F_b598c D_b598c.
             stepb_tk F_b5990 D_b5990 ltac:(condw tw_hit).
             stepn F_b59c4 D_b59c4.
             mlbu F_b59c8 D_b59c8 j.
             stepb_tk F_b59cc D_b59cc ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
          destruct (t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    -
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb780c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 8) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 (m - 8) /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * mld F_b597c D_b597c j.
          stepn F_b5980 D_b5980.
          stepn F_b5984 D_b5984.
          stepn F_b5988 D_b5988.
          stepn F_b598c D_b598c.
          stepb_ft F_b5990 D_b5990 ltac:(condw tw_miss).
          stepn F_b5994 D_b5994.
          stepn F_b5998 D_b5998.
          stepb_tk F_b599c D_b599c ltac:(cond).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC).
        destruct (IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
                    ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  Ltac ldc F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
          exact RD
        | assumption ]
      | step_simpl]; vnorm.

  Lemma a_entry : forall regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 1 ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb77dc : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret j m Hret H1 H10 H11 H12 H14 Hj Hal Hm.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (al_room j Hal Hj) as HR.
    destruct (rd_const_M mem Hro) as (bsM & RM & EM).
    destruct (rd_const_H mem Hro) as (bsH & RH & EH).
    destruct (Z.eq_dec j K) as [HjK|HjK].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7838 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_b594c D_b594c ltac:(cond).
          mlbu F_b5950 D_b5950 j.
          stepb_tk F_b5954 D_b5954 ltac:(condb).
          stepn F_b59a0 D_b59a0.
          stepb_ft F_b59a4 D_b59a4 ltac:(cond).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & KC).
        destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb780c : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 m /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_b594c D_b594c ltac:(cond).
          mlbu F_b5950 D_b5950 j.
          stepb_ft F_b5954 D_b5954 ltac:(condb).
          stepn F_b5958 D_b5958.
          stepb_ft F_b595c D_b595c ltac:(cond).
          stepn F_b5960 D_b5960.
          ldc F_b5964 D_b5964 (Z_to_bv 64 Mc) RM.
          stepn F_b5968 D_b5968.
          ldc F_b596c D_b596c (Z_to_bv 64 Hc) RH.
          stepn F_b5970 D_b5970.
          stepiv F_b5974 D_b5974 (Z_to_bv 64 0)
            ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
          vnorm.
          stepn F_b5978 D_b5978.
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC).
        destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  Ltac snez1 :=
    match goal with |- context [v_sltu ?a ?b] =>
      replace (v_sltu a b) with (Z_to_bv 64 1)
        by (symmetry; rwH; unfold v_sltu; rewrite c_ltu_ltb; try unfold v_addi; unorm;
            rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity) end.

  Lemma andi7_u : forall j, (0 <= bv_unsigned s + j < 2 ^ 64)%Z ->
    bv_unsigned (v_andi (at_ s j) 7) = ((bv_unsigned s + j) mod 8)%Z.
  Proof.
    intros j Hj. rewrite u_andi by lia. rewrite at_u by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma h_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 15 = at_ s (j + 1) -> getr regs 16 = Z_to_bv 64 1 ->
    (0 <= j <= K)%Z -> (Z.of_nat i = 7 - (bv_unsigned s + j) mod 8)%Z -> (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0xb77b4 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H15 H16 Hj Hi Hm.
    -
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7838 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_b5924 D_b5924 j.
             stepn F_b5928 D_b5928.
             stepb_tk F_b592c D_b592c ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & KC).
          destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xb77dc : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_b5924 D_b5924 j.
             stepn F_b5928 D_b5928.
             stepb_ft F_b592c D_b592c ltac:(condb).
             stepn F_b5930 D_b5930.
             stepn F_b5934 D_b5934.
             stepn F_b5938 D_b5938.
             stepn F_b593c D_b593c. snez1.
             stepb_tk F_b5940 D_b5940
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                     rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                     replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
          destruct (a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    -
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7838 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_b5924 D_b5924 j.
             stepn F_b5928 D_b5928.
             stepb_tk F_b592c D_b592c ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & KC).
          destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
        assert (HM : ((bv_unsigned s + j + 1) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
        { clear -Hi Hs Hj. rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j)).
          pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). apply Z.mod_small. lia. }
        eapply (runs_trans RSEGS _ (fun r => mkst r (0xb77b4 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 15 = at_ s (j + 1 + 1)
                           /\ getr r 16 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_b5924 D_b5924 j.
             stepn F_b5928 D_b5928.
             stepb_ft F_b592c D_b592c ltac:(condb).
             stepn F_b5930 D_b5930.
             stepn F_b5934 D_b5934.
             stepn F_b5938 D_b5938.
             stepn F_b593c D_b593c. snez1.
             stepb_ft F_b5940 D_b5940
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).
             stepn F_b5944 D_b5944.
             stepb_tk F_b5948 D_b5948 ltac:(cond).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
          destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  Lemma memchr0_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0xb7798 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. rewrite <- (at_0 s) in H10.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb77dc : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_b5908 D_b5908. rwH. vals_lit.
          stepn F_b590c D_b590c.
          stepn F_b5910 D_b5910. snez1.
          stepb_tk F_b5914 D_b5914
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_0_r; exact Hal).
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
        destruct (a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    -
      eapply (runs_trans RSEGS _ (fun r => mkst r (0xb77b4 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                         /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_b5908 D_b5908. rwH. vals_lit.
          stepn F_b590c D_b590c.
          stepn F_b5910 D_b5910. snez1.
          stepb_ft F_b5914 D_b5914
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_0_r; exact Hal).
          stepb_ft F_b5918 D_b5918 ltac:(cond).
          stepn F_b591c D_b591c.
          stepn F_b5920 D_b5920.
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
        destruct (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

End MCHR.

Theorem ref_memchr0 : forall mem (s : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps RSEGS (mkst regs (0xb7798 : word) mem rom) (mkst regs' ret mem rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned s + K).
Proof.
  intros mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12.
  destruct (memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12) as (r & RUN & A10 & KC).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.

End FPX_1.
