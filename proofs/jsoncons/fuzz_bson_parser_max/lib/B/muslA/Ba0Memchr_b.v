(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0MemcpyBase_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_rcb2e4_cbd08_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Mc : Z := 0x0101010101010100.   (* [comment removed for export] *)
Definition Hc : Z := 0x8080808080808080.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LDv (l : list byte) : word := Z_to_bv 64 (bytes_le_to_Z l).

Lemma u_LDv : forall l, length l = 8%nat -> bv_unsigned (LDv l) = bytes_le_to_Z l.
Proof. intros l H. unfold LDv. pose proof (bytes_le_to_Z_range l H). apply u_Z2bv; lia. Qed.

(* [comment removed for export] *)
Definition TW (x : word) : word :=
  v_and (v_or (v_sub (Z_to_bv 64 Mc) (v_xor x (Z_to_bv 64 0))) (v_xor x (Z_to_bv 64 0))) (Z_to_bv 64 Hc).

Lemma v_xor_0 : forall x : word, v_xor x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_xor. rewrite (u_Z2bv 0) by lia. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma TW_bits : forall x : word, let y := bv_unsigned x in
  (forall i, (0 <= i)%Z ->
     Z.testbit (bv_unsigned (TW x)) i = (Z.testbit Hc i && negb (Z.testbit (HZ.Tz y) i))%bool)
  /\ (forall i, (0 <= i)%Z -> Z.testbit (HZ.Tz y) i = true -> Z.testbit Hc i = true).
Proof.
  intros x y. pose proof (u64_range x) as Hx. subst y.
  assert (A64 : (0 <= (bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  set (A := ((bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64)%Z) in *.
  (* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x103b0 <= i < 0x103d0)%Z -> mem (Z_to_bv 64 i) = None.

Lemma rd_const_M : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x103c8) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Mc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 66504)) with 66504%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 66504)) with 66504%Z in Hx. cbn in Hx. lia.
Qed.

Lemma rd_const_H : forall mem, rodata_clear mem ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 0x103b0) 8 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 Hc).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 66480)) with 66480%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 66480)) with 66480%Z in Hx. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_sub : forall (bs : list byte) j m i d,
  (i < m)%nat -> (j + m <= length bs)%nat -> nth i (sub bs j m) d = nth (j + i) bs d.
Proof.
  intros bs j m i d Hi Hjm. unfold sub.
  rewrite nth_firstn. replace (i <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c_eq_LBv_0 : forall b : byte, c_eq (LBv b) (Z_to_bv 64 0) = (bv_unsigned b =? 0)%Z.
Proof.
  intros b. unfold c_eq, bv_eqb, LBv. pose proof (bv_unsigned_in_range _ b) as R.
  change (bv_modulus 8) with 256%Z in R.
  rewrite (u_Z2bv (bv_unsigned b)) by lia. rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Ltac condb :=
    rwH; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].
  (* [comment removed for export] *)
  Ltac cond := try unfold v_addi; cond_lia.
  (* [comment removed for export] *)
  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ (v_xor ?x _)) _) _) _ = ?b =>
      change (c_eq (TW x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; unorm; f_equal; lia); try solve_keeps_cs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_found : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s K -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps RSEGS (mkst regs (0x1298a4 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11. pose proof KL. eexists. split.
    - mlbu F_1272b4 D_1272b4 K.                       (* [comment removed for export] *)
      stepb_tk F_1272b8 D_1272b8 ltac:(condb).        (* [comment removed for export] *)
      stepret F_1272cc D_1272cc ret ltac:(exact H1).
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 13 = Z_to_bv 64 m ->
    (0 <= j < K)%Z -> (Z.of_nat i = K - 1 - j)%Z -> (K - j + 1 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x1298ac : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H13 Hj Hi Hm.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_1272bc D_1272bc.                      (* [comment removed for export] *)
        stepn F_1272c0 D_1272c0.                      (* [comment removed for export] *)
        stepb_tk F_1272c4 D_1272c4 ltac:(cond).       (* [comment removed for export] *)
        mlbu F_1272b4 D_1272b4 K.                     (* [comment removed for export] *)
        stepb_tk F_1272b8 D_1272b8 ltac:(condb).      (* [comment removed for export] *)
        stepret F_1272cc D_1272cc ret ltac:(exact H1).
        apply mst_refl.
      + post.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x1298ac : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 13 = Z_to_bv 64 (m - 1) /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_1272bc D_1272bc.                    (* [comment removed for export] *)
          stepn F_1272c0 D_1272c0.                    (* [comment removed for export] *)
          stepb_tk F_1272c4 D_1272c4 ltac:(cond).     (* [comment removed for export] *)
          mlbu F_1272b4 D_1272b4 (j + 1)%Z.           (* [comment removed for export] *)
          stepb_ft F_1272b8 D_1272b8 ltac:(condb).    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
        destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_loop : forall (i : nat) regs (ret : word) j m,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = at_ s j -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 m -> getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 7 ->
    (0 <= j <= K)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    (K - j + 8 <= m < 2 ^ 64)%Z ->
    exists regs',
      msteps RSEGS (mkst regs (0x129878 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3).
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H13 H14 H15 H16 Hj Hal Hi Hm;
      pose proof (al_room j Hal Hj) as HR.
    - (* [comment removed for export] *)
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + (* [comment removed for export] *)
        eexists. split.
        * mld F_127288 D_127288 j.                    (* [comment removed for export] *)
          stepn F_12728c D_12728c.                    (* [comment removed for export] *)
          stepn F_127290 D_127290.                    (* [comment removed for export] *)
          stepn F_127294 D_127294.                    (* [comment removed for export] *)
          stepn F_127298 D_127298.                    (* [comment removed for export] *)
          stepb_tk F_12729c D_12729c ltac:(condw tw_hit).   (* [comment removed for export] *)
          stepn F_1272d0 D_1272d0.                    (* [comment removed for export] *)
          mlbu F_1272d4 D_1272d4 j.                   (* [comment removed for export] *)
          stepb_ft F_1272d8 D_1272d8 ltac:(condb).    (* [comment removed for export] *)
          stepn F_1272dc D_1272dc.                    (* [comment removed for export] *)
          stepret F_1272cc D_1272cc ret ltac:(exact H1).
          apply mst_refl.
        * post.
      + (* [comment removed for export] *)
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x1298ac : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 13 = Z_to_bv 64 m /\ keeps_cs regs r)).
        * eexists. split.
          -- mld F_127288 D_127288 j.
             stepn F_12728c D_12728c.
             stepn F_127290 D_127290.
             stepn F_127294 D_127294.
             stepn F_127298 D_127298.
             stepb_tk F_12729c D_12729c ltac:(condw tw_hit).
             stepn F_1272d0 D_1272d0.                 (* [comment removed for export] *)
             mlbu F_1272d4 D_1272d4 j.                (* [comment removed for export] *)
             stepb_tk F_1272d8 D_1272d8 ltac:(condb). (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R13 & KC).
          destruct (t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x129878 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 8) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 (m - 8) /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * mld F_127288 D_127288 j.
          stepn F_12728c D_12728c.
          stepn F_127290 D_127290.
          stepn F_127294 D_127294.
          stepn F_127298 D_127298.
          stepb_ft F_12729c D_12729c ltac:(condw tw_miss).  (* [comment removed for export] *)
          stepn F_1272a0 D_1272a0.                    (* [comment removed for export] *)
          stepn F_1272a4 D_1272a4.                    (* [comment removed for export] *)
          stepb_tk F_1272a8 D_1272a8 ltac:(cond).     (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x129848 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret j m Hret H1 H10 H11 H12 H14 Hj Hal Hm.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (al_room j Hal Hj) as HR.
    destruct (rd_const_M mem Hro) as (bsM & RM & EM).
    destruct (rd_const_H mem Hro) as (bsH & RH & EH).
    destruct (Z.eq_dec j K) as [HjK|HjK].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x1298a4 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_127258 D_127258 ltac:(cond).     (* [comment removed for export] *)
          mlbu F_12725c D_12725c j.                   (* [comment removed for export] *)
          stepb_tk F_127260 D_127260 ltac:(condb).    (* [comment removed for export] *)
          stepn F_1272ac D_1272ac.                    (* [comment removed for export] *)
          stepb_ft F_1272b0 D_1272b0 ltac:(cond).     (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & KC).
        destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x129878 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 m /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_127258 D_127258 ltac:(cond).     (* [comment removed for export] *)
          mlbu F_12725c D_12725c j.                   (* [comment removed for export] *)
          stepb_ft F_127260 D_127260 ltac:(condb).    (* [comment removed for export] *)
          stepn F_127264 D_127264.                    (* [comment removed for export] *)
          stepb_ft F_127268 D_127268 ltac:(cond).     (* [comment removed for export] *)
          stepn F_12726c D_12726c.                    (* [comment removed for export] *)
          ldc F_127270 D_127270 (Z_to_bv 64 Mc) RM.   (* [comment removed for export] *)
          stepn F_127274 D_127274.                    (* [comment removed for export] *)
          ldc F_127278 D_127278 (Z_to_bv 64 Hc) RH.   (* [comment removed for export] *)
          stepn F_12727c D_12727c.                    (* [comment removed for export] *)
          stepiv F_127280 D_127280 (Z_to_bv 64 0)
            ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
          vnorm.
          stepn F_127284 D_127284.                    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC).
        destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
      msteps RSEGS (mkst regs (0x129820 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H15 H16 Hj Hi Hm.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x1298a4 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_127230 D_127230 j.                (* [comment removed for export] *)
             stepn F_127234 D_127234.                 (* [comment removed for export] *)
             stepb_tk F_127238 D_127238 ltac:(condb). (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & KC).
          destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x129848 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_127230 D_127230 j.                (* [comment removed for export] *)
             stepn F_127234 D_127234.                 (* [comment removed for export] *)
             stepb_ft F_127238 D_127238 ltac:(condb). (* [comment removed for export] *)
             stepn F_12723c D_12723c.                 (* [comment removed for export] *)
             stepn F_127240 D_127240.                 (* [comment removed for export] *)
             stepn F_127244 D_127244.                 (* [comment removed for export] *)
             stepn F_127248 D_127248. snez1.          (* [comment removed for export] *)
             stepb_tk F_12724c D_12724c
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                     rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                     replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity).  (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
          destruct (a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x1298a4 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_127230 D_127230 j.
             stepn F_127234 D_127234.
             stepb_tk F_127238 D_127238 ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & KC).
          destruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
        assert (HM : ((bv_unsigned s + j + 1) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
        { clear -Hi Hs Hj. rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j)).
          pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). apply Z.mod_small. lia. }
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x129820 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 15 = at_ s (j + 1 + 1)
                           /\ getr r 16 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_127230 D_127230 j.                (* [comment removed for export] *)
             stepn F_127234 D_127234.                 (* [comment removed for export] *)
             stepb_ft F_127238 D_127238 ltac:(condb). (* [comment removed for export] *)
             stepn F_12723c D_12723c.                 (* [comment removed for export] *)
             stepn F_127240 D_127240.                 (* [comment removed for export] *)
             stepn F_127244 D_127244.                 (* [comment removed for export] *)
             stepn F_127248 D_127248. snez1.          (* [comment removed for export] *)
             stepb_ft F_12724c D_12724c
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).     (* [comment removed for export] *)
             stepn F_127250 D_127250.                 (* [comment removed for export] *)
             stepb_tk F_127254 D_127254 ltac:(cond).  (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
          destruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memchr0_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x129804 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = at_ s K /\ keeps_cs regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. rewrite <- (at_0 s) in H10.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x129848 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_127214 D_127214. rwH. vals_lit.     (* [comment removed for export] *)
          stepn F_127218 D_127218.                    (* [comment removed for export] *)
          stepn F_12721c D_12721c. snez1.             (* [comment removed for export] *)
          stepb_tk F_127220 D_127220
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R14 & KC).
        destruct (a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x129820 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                         /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_127214 D_127214. rwH. vals_lit.     (* [comment removed for export] *)
          stepn F_127218 D_127218.                    (* [comment removed for export] *)
          stepn F_12721c D_12721c. snez1.             (* [comment removed for export] *)
          stepb_ft F_127220 D_127220
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          stepb_ft F_127224 D_127224 ltac:(cond).     (* [comment removed for export] *)
          stepn F_127228 D_127228.                    (* [comment removed for export] *)
          stepn F_12722c D_12722c.                    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & R16 & KC).
        destruct (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

End MCHR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ref_memchr0 : forall mem (s : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps RSEGS (mkst regs (0x129804 : word) mem rom) (mkst regs' ret mem rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned s + K).
Proof.
  intros mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12.
  destruct (memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12) as (r & RUN & A10 & KC).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.

End FPX_1.
