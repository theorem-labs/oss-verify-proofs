(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec SymStepR StepTac StoreOk AgentLib StartupTac StartupAux RefMemcpyLib RefEnframeArith MemSplit SumsLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRPLib AsanPlanImages AsanIMemcpy.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Asan_code_depot1 AsanDepotMem AsanDepotInv AsanDepotWalkL AsanDepotWalkS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.AsanRPLib.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.SymStepR.asanreflect_fx.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma step_fence : forall regs pc mem rom w a b c d e,
  fetch_word SEGS pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof. intros. rewrite <- !mkstR_None. eapply stepR_fence; eassumption. Qed.
Ltac afence F D := chain_step; [reflexivity | eapply step_fence; [exact F | reflexivity | exact D] | step_simpl].

(* [comment removed for export] *)
Lemma rdn_rom : forall k mem (a : word),
  (forall i, (i < k)%nat -> seg_rom SEGS (a + nat_to_word i) <> None) ->
  exists bs, rdn SEGS mem a k = Some bs.
Proof.
  induction k as [|k IH]; intros mem a H; [exists []; reflexivity|].
  cbn [rdn].
  assert (H0 : seg_rom SEGS a <> None).
  { specialize (H 0%nat ltac:(lia)). rewrite word_add_0 in H. exact H. }
  destruct (IH mem (a + 1)) as (bs & Hbs).
  { intros i Hi. replace (a + 1 + nat_to_word i) with (a + nat_to_word (S i)). { apply H. lia. }
    rewrite !at_nat, word_succ_at, at_at. f_equal. lia. }
  destruct (mem a) as [b|].
  - rewrite Hbs. eexists. reflexivity.
  - destruct (seg_rom SEGS a) as [b|]; [|exfalso; apply H0; reflexivity]. rewrite Hbs. eexists. reflexivity.
Qed.

Lemma rom8_10310 : forall mem, exists bs, rdn SEGS mem (Z_to_bv 64 66320) 8 = Some bs.
Proof. intros. replace (Z_to_bv 64 66320) with (66320 : word) by (apply bv_eq; reflexivity). apply rdn_rom. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma rom8_103b0 : forall mem, exists bs, rdn SEGS mem (Z_to_bv 64 66480) 8 = Some bs.
Proof. intros. replace (Z_to_bv 64 66480) with (66480 : word) by (apply bv_eq; reflexivity). apply rdn_rom. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.
Lemma rom8_102e8 : forall mem, exists bs, rdn SEGS mem (Z_to_bv 64 66280) 8 = Some bs.
Proof. intros. replace (Z_to_bv 64 66280) with (66280 : word) by (apply bv_eq; reflexivity). apply rdn_rom. intros i Hi. do 8 (destruct i as [|i]; [vm_compute; discriminate|]). lia. Qed.

(* [comment removed for export] *)
Lemma rdn8_word : forall mem a bs, rdn SEGS mem a 8 = Some bs ->
  bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
Proof.
  intros mem a bs H. pose proof (rdn_length _ _ _ _ _ H) as L.
  pose proof (bytes_le_to_Z_bound bs) as B0. pose proof (bytes_le_to_Z_nonneg bs) as B1. rewrite L in B0.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B0. rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sextw_size : forall size tag, (0 <= size < 2 ^ 31)%Z -> (0 <= tag < 2 ^ 32)%Z ->
  v_addiw (Z_to_bv 64 (size + tag * 2 ^ 32)) 0 = Z_to_bv 64 size.
Proof.
  intros size tag Hs Ht. unfold v_addiw. rewrite u64_lit by lia. rewrite Z.add_0_r.
  rewrite swrap32_add_mod. rewrite swrap32_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bucket_off : forall h : word,
  v_srli (v_slli h 44) 42 = Z_to_bv 64 (4 * (bv_unsigned h mod 2 ^ 20)).
Proof.
  intros h. pose proof (u64_range h) as Hh. unfold v_srli, v_slli.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 44 * 2 ^ 20)%Z.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. f_equal.
  set (u := bv_unsigned h) in *.
  rewrite (Z.mul_comm u (2 ^ 44)), Z.mul_mod_distr_l by lia.
  change (2 ^ 44)%Z with (2 ^ 42 * 4)%Z.
  rewrite <- Z.mul_assoc, (Z.mul_comm (2 ^ 42)), Z.div_mul by lia. reflexivity.
Qed.

Ltac post_regs :=
  repeat split; gr; rewrite ?v_addi_0; try reflexivity; try assumption; try (f_equal; lia);
  try (lazymatch goal with |- ?a = ?b => check_closed_term a; check_closed_term b; apply bv_eq; vm_compute; reflexivity end);
  let x := fresh "x" in intros x; intros;
  repeat (rewrite getr_other by assumption); try reflexivity.

Section PUT.
  Variables (mem rom : word -> option byte) (usp T w size tag : Z) (bs : list byte) (ret : word).
  Variables (n B P tf st : Z) (tab lnk : Z -> Z) (hsh : Z -> word).

  Hypothesis Husp : (2 ^ 32 <= usp - 224)%Z /\ (usp < 2 ^ 64)%Z.
  Hypothesis Hstk : okr mem (usp - 224) 224.
  Hypothesis HT : (2 ^ 32 <= T)%Z /\ (T + 8 * size < 2 ^ 64)%Z.
  Hypothesis HTrd : rdn SEGS mem (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs.
  Hypothesis HTstk : (T + 8 * size <= usp - 224 \/ usp <= T)%Z.
  Hypothesis Hw : w = (size + tag * 2 ^ 32)%Z /\ (1 <= size <= 255)%Z /\ (0 <= tag < 256)%Z.
  (* [comment removed for export] *)
  Hypothesis Hn : (0 <= n)%Z /\ (n + 1 < 2 ^ 16)%Z.
  Hypothesis Htab : forall b, (0 <= b < 2 ^ 20)%Z -> cell32 mem (DEPOT + 4 * b) (tab b) /\ (0 <= tab b <= n)%Z.
  Hypothesis Hnid : cell32 mem NIDS n.
  Hypothesis Hmap : cell64 mem MAP1 B.
  Hypothesis HB : (0x608000 <= B)%Z /\ (B + 16 * 2 ^ 16 < 2 ^ 64)%Z.
  Hypothesis Hnodes : forall id, (1 <= id <= n)%Z ->
    rdn SEGS mem (Z_to_bv 64 (B + 16 * id)) 8 = Some (word_to_le_bytes 8 (hsh id))
    /\ cell32 mem (B + 16 * id + 8) (lnk id) /\ (0 <= lnk id < id)%Z.
  Hypothesis Hnew : okr mem (B + 16 * (n + 1)) 16.
  Hypothesis HBstk : (usp <= B + 16 \/ B + 16 * (n + 2) <= usp - 224)%Z.
  Hypothesis HBT : (T + 8 * size <= B + 16 * (n + 1) \/ B + 16 * (n + 2) <= T)%Z.
  Hypothesis HBP : (P + 8 * tf + 8 * (size + 1) <= B + 16 \/ B + 16 * (n + 2) <= P + 8 * tf)%Z.
  (* [comment removed for export] *)
  Hypothesis Htf : cell64 mem SSB tf.
  Hypothesis HP : cell64 mem (SSB + 16) P.
  Hypothesis Hst : cell32 mem (SSB + 24) st.
  Hypothesis Hroom : (0 <= tf)%Z /\ (tf + 256 < 2 ^ 20)%Z /\ (0 <= st)%Z /\ (st + 256 < 2 ^ 20)%Z.
  Hypothesis HPblk : (0x608000 <= P)%Z /\ (P + 8 * 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis HPok : okr mem (P + 8 * tf) (8 * (size + 1)).
  Hypothesis HPstk : (usp <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= usp - 224)%Z.
  Hypothesis HTP : (T + 8 * size <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= T)%Z.
  Hypothesis Hret : ret_ok ret.

  Let LENBS : length bs = Z.to_nat (8 * size).
  Proof. exact (rdn_length _ _ _ _ _ HTrd). Qed.
  Ltac peelp := repeat (rewrite rdn_wbytes_out by (rewrite ?length_N_to_le_bytes, ?LENBS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).

  Definition put_frame (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 vra))
      (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 v8))
      (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 v9))
      (Z_to_bv 64 (usp - 32)) (word_to_le_bytes 8 v18))
      (Z_to_bv 64 (usp - 40)) (word_to_le_bytes 8 v19))
      (Z_to_bv 64 (usp - 48)) (word_to_le_bytes 8 v20))
      (Z_to_bv 64 (usp - 56)) (word_to_le_bytes 8 v21))
      (Z_to_bv 64 (usp - 64)) (word_to_le_bytes 8 v22))
      (Z_to_bv 64 (usp - 72)) (word_to_le_bytes 8 v23))
      (Z_to_bv 64 (usp - 80)) (word_to_le_bytes 8 v24))
      (Z_to_bv 64 (usp - 88)) (word_to_le_bytes 8 v25))
      (Z_to_bv 64 (usp - 104)) (word_to_le_bytes 8 (Z_to_bv 64 T)))
      (Z_to_bv 64 (usp - 96)) (word_to_le_bytes 8 (Z_to_bv 64 w)).
  #[local] Notation PF regs := (put_frame ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                                          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)).

  (* [comment removed for export] *)
  #[using="tag bs n B P tf st Husp Hstk HT HTrd Hw Hn HB HBstk HBP Hroom HPblk HPstk LENBS"] Lemma put_pro : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 T -> getr regs 11 = Z_to_bv 64 w ->
    exists r1,
      msteps SEGS (mkst regs (0x74d04 : word) mem rom) (mkst r1 (0x74d7c : word) (PF regs) rom)
      /\ getr r1 2 = Z_to_bv 64 (usp - 112) /\ getr r1 8 = Z_to_bv 64 0 /\ getr r1 9 = Z_to_bv 64 DEPOT
      /\ getr r1 11 = Z_to_bv 64 T /\ getr r1 12 = Z_to_bv 64 w /\ getr r1 13 = Z_to_bv 64 size
      /\ (forall r, r <> 2 -> r <> 8 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> getr r1 r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11. pose proof Hw as (Ew & Hsz & Htg).
    eexists. split.
    - ai F_74d04 D_74d04.
      ai F_74d08 D_74d08.
      ai F_74d0c D_74d0c.
      ai F_74d10 D_74d10.
      ai F_74d14 D_74d14.
      ai F_74d18 D_74d18.
      ai F_74d1c D_74d1c.
      stepj F_74d20 D_74d20.
      ai F_74d24 D_74d24.
      ast F_74d28 D_74d28 (Z_to_bv 64 (usp - 8)) ret ltac:(okw Hstk).
      ast F_74d2c D_74d2c (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okw Hstk).
      ast F_74d30 D_74d30 (Z_to_bv 64 (usp - 24)) (getr regs 9) ltac:(okw Hstk).
      ast F_74d34 D_74d34 (Z_to_bv 64 (usp - 32)) (getr regs 18) ltac:(okw Hstk).
      ast F_74d38 D_74d38 (Z_to_bv 64 (usp - 40)) (getr regs 19) ltac:(okw Hstk).
      ast F_74d3c D_74d3c (Z_to_bv 64 (usp - 48)) (getr regs 20) ltac:(okw Hstk).
      ast F_74d40 D_74d40 (Z_to_bv 64 (usp - 56)) (getr regs 21) ltac:(okw Hstk).
      ast F_74d44 D_74d44 (Z_to_bv 64 (usp - 64)) (getr regs 22) ltac:(okw Hstk).
      ast F_74d48 D_74d48 (Z_to_bv 64 (usp - 72)) (getr regs 23) ltac:(okw Hstk).
      ast F_74d4c D_74d4c (Z_to_bv 64 (usp - 80)) (getr regs 24) ltac:(okw Hstk).
      ast F_74d50 D_74d50 (Z_to_bv 64 (usp - 88)) (getr regs 25) ltac:(okw Hstk).
      ai F_74d54 D_74d54.
      ai F_74d58 D_74d58.
      ast F_74d5c D_74d5c (Z_to_bv 64 (usp - 104)) (Z_to_bv 64 T) ltac:(okw Hstk).
      ast F_74d60 D_74d60 (Z_to_bv 64 (usp - 96)) (Z_to_bv 64 w) ltac:(okw Hstk).
      match goal with |- context [mkst _ _ (wbytes ?m ?a ?v) _] =>
        change (wbytes m a v) with (PF regs) end.
      (* [comment removed for export] *)
      stepb_tk F_74d64 D_74d64 ltac:(pin; reflexivity).
      (* [comment removed for export] *)
      ai F_74d6c D_74d6c. rewrite Ew, sextw_size by lia. rewrite <- Ew.
      ai F_74d70 D_74d70.
      (* [comment removed for export] *)
      stepb_ft F_74d74 D_74d74 ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
      stepb_ft F_74d78 D_74d78 ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
      apply mst_refl.
    - post_regs.
  Qed.

  (* [comment removed for export] *)
  #[using="mem usp w tag n B P tf st Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma trace_word : forall m k, rdn SEGS m (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs -> (0 <= k < size)%Z ->
    exists v : word, rdn SEGS m (Z_to_bv 64 (T + 8 * k)) 8 = Some (word_to_le_bytes 8 v).
  Proof.
    intros m k H Hk.
    pose proof (rdn_sub SEGS m (Z.to_nat (8 * size)) (Z_to_bv 64 T) bs (Z.to_nat (8 * k)) 8 H ltac:((ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @Hk]); lia))) as R.
    unfold at_ in R. rewrite u64_lit in R by lia. rewrite Z2Nat.id in R by lia.
    pose proof (sub_length bs (Z.to_nat (8 * k)) 8 ltac:(rewrite LENBS; (ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @Hk]); lia))) as L.
    exists (Z_to_bv 64 (lez (sub bs (Z.to_nat (8 * k)) 8))). rewrite R. f_equal.
    pose proof (lez_bound_len _ _ L) as B0. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B0.
    unfold word_to_le_bytes. rewrite u64_lit by lia. symmetry. etransitivity; [|apply Z_to_le_bytes_lez]. rewrite L. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="mem usp bs n B P tf st Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma hash_pre : forall m regs,
    getr regs 11 = Z_to_bv 64 T -> getr regs 12 = Z_to_bv 64 w ->
    exists r1 (mul h0 : word),
      msteps SEGS (mkst regs (0x74d7c : word) m rom) (mkst r1 (0x74db4 : word) m rom)
      /\ getr r1 11 = Z_to_bv 64 T /\ getr r1 14 = Z_to_bv 64 (T + 8 * size) /\ getr r1 13 = Z_to_bv 64 tag
      /\ getr r1 10 = mul /\ getr r1 12 = h0
      /\ (forall r, r <> 10 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 -> getr r1 r = getr regs r).
  Proof.
    intros m regs H11 H12. pose proof Hw as (Ew & Hsz & Htg).
    assert (Hwr : (0 <= w < 2 ^ 64)%Z) by (rewrite Ew; (ltac2:(LK.k [@Husp; @HT; @HTstk; @Hn; @HB; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @Hsz; @Htg]); lia)).
    assert (Hhi : (w / 2 ^ 32 = tag)%Z) by (rewrite Ew, Z.div_add by lia; rewrite Z.div_small by lia; lia).
    assert (Hlo : (Z.land w 4294967295 = size)%Z).
    { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Ew. change (2 ^ Z.of_N 32)%Z with (2 ^ 32)%Z.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (rom8_10310 m) as (c1 & Hc1). destruct (rom8_103b0 m) as (c2 & Hc2). destruct (rom8_102e8 m) as (c3 & Hc3).
    eexists _, _, _. split.
    - ai F_74d7c D_74d7c. rewrite v_srli_lit, Hhi by lia.
      ai F_74d80 D_74d80.
      ai F_74d84 D_74d84.
      ai F_74d88 D_74d88.
      ai F_74d8c D_74d8c.
      ld_step F_74d90 D_74d90 c1 (Z_to_bv 64 (lez c1)) ltac:(exact Hc1) ltac:(exact (rdn8_word _ _ _ Hc1)).
      ai F_74d94 D_74d94. rewrite v_and_lit, Hlo by lia.
      ai F_74d98 D_74d98.
      ld_step F_74d9c D_74d9c c2 (Z_to_bv 64 (lez c2)) ltac:(exact Hc2) ltac:(exact (rdn8_word _ _ _ Hc2)).
      ld_step F_74da0 D_74da0 c3 (Z_to_bv 64 (lez c3)) ltac:(exact Hc3) ltac:(exact (rdn8_word _ _ _ Hc3)).
      ai F_74da4 D_74da4.
      ai F_74da8 D_74da8. rewrite v_slli_lit by lia.
      ai F_74dac D_74dac.
      ai F_74db0 D_74db0.
      apply mst_refl.
    - post_regs.
  Qed.

  (* [comment removed for export] *)
  #[using="mem usp w tag n B P tf st Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma hash_loop : forall m (i : nat) regs k (mul : word),
    rdn SEGS m (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs ->
    getr regs 11 = Z_to_bv 64 (T + 8 * k) -> getr regs 14 = Z_to_bv 64 (T + 8 * size) -> getr regs 10 = mul ->
    (0 <= k < size)%Z -> Z.of_nat i = (size - 1 - k)%Z ->
    exists r1 (h1 : word),
      msteps SEGS (mkst regs (0x74db4 : word) m rom) (mkst r1 (0x74dd8 : word) m rom)
      /\ getr r1 12 = h1 /\ getr r1 10 = mul
      /\ (forall r, r <> 11 -> r <> 12 -> r <> 15 -> r <> 16 -> getr r1 r = getr regs r).
  Proof.
    intros m i. induction i as [|i IH]; intros regs k mul HTm H11 H14 H10 Hk Hi.
    - destruct (trace_word m k HTm Hk) as (v & Hv).
      eexists _, _. split.
      + ld_step F_74db4 D_74db4 (word_to_le_bytes 8 v) v ltac:(rewrite ?Z.add_0_r; exact Hv) ltac:(apply bytes_le_to_Z_8).
        ai F_74db8 D_74db8.
        ai F_74dbc D_74dbc.
        ai F_74dc0 D_74dc0.
        ai F_74dc4 D_74dc4.
        ai F_74dc8 D_74dc8.
        ai F_74dcc D_74dcc.
        ai F_74dd0 D_74dd0.
        stepb_ft F_74dd4 D_74dd4 ltac:(pin; rewrite c_eq_zbv by (ltac2:(LK.k [@Husp; @HT; @HTstk; @Hn; @HB; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @HTP; @LENBS; @Hk; @Hi; @HBT]); lia); apply Z.eqb_eq; (ltac2:(LK.k [@Husp; @HT; @HTstk; @Hn; @HB; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @HTP; @LENBS; @Hk; @Hi; @HBT]); lia)).
        apply mst_refl.
      + post_regs.
    - destruct (trace_word m k HTm Hk) as (v & Hv).
      assert (STEP : exists r0 (h0 : word),
        msteps SEGS (mkst regs (0x74db4 : word) m rom) (mkst r0 (0x74db4 : word) m rom)
        /\ getr r0 11 = Z_to_bv 64 (T + 8 * (k + 1)) /\ getr r0 14 = Z_to_bv 64 (T + 8 * size) /\ getr r0 10 = mul /\ getr r0 12 = h0
        /\ (forall r, r <> 11 -> r <> 12 -> r <> 15 -> r <> 16 -> getr r0 r = getr regs r)).
      { eexists _, _. split.
        + ld_step F_74db4 D_74db4 (word_to_le_bytes 8 v) v ltac:(rewrite ?Z.add_0_r; exact Hv) ltac:(apply bytes_le_to_Z_8).
          ai F_74db8 D_74db8.
          ai F_74dbc D_74dbc.
          ai F_74dc0 D_74dc0.
          ai F_74dc4 D_74dc4.
          ai F_74dc8 D_74dc8.
          ai F_74dcc D_74dcc.
          ai F_74dd0 D_74dd0.
          stepb_tk F_74dd4 D_74dd4 ltac:(pin; rewrite c_eq_zbv by (ltac2:(LK.k [@Husp; @HT; @HTstk; @Hw; @Hn; @HB; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @HTP; @LENBS; @Hk; @Hi; @HBT]); lia); apply Z.eqb_neq; (ltac2:(LK.k [@Husp; @HT; @HTstk; @Hw; @Hn; @HB; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @HTP; @LENBS; @Hk; @Hi; @HBT]); lia)).
          apply mst_refl.
        + post_regs. }
      destruct STEP as (r0 & h0 & RUN0 & Q11 & Q14 & Q10 & Q12 & QR).
      destruct (IH r0 (k + 1)%Z mul HTm Q11 Q14 Q10 ltac:((ltac2:(LK.k [@HTstk; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @Hk; @Hi]); lia)) ltac:((ltac2:(LK.k [@HTstk; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @Hk; @Hi]); lia))) as (r1 & h1 & RUN1 & P12 & P10 & PR).
      exists r1, h1. split; [eapply msteps_trans; [exact RUN0 | exact RUN1]|].
      split; [exact P12|]. split; [exact P10|].
      intros r N11 N12 N15 N16. rewrite PR by assumption. apply QR; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="mem usp T w size bs B P tf HTrd HTstk Hw Hn HBstk HBT HBP HPstk HTP LENBS"] Lemma hash_fin : forall m regs (mul h1 : word),
    (forall b, (0 <= b < 2 ^ 20)%Z -> cell32 m (DEPOT + 4 * b) (tab b) /\ (0 <= tab b <= n)%Z) ->
    getr regs 9 = Z_to_bv 64 DEPOT -> getr regs 13 = Z_to_bv 64 tag -> getr regs 10 = mul -> getr regs 12 = h1 ->
    exists r1 (h : word) bkt,
      msteps SEGS (mkst regs (0x74dd8 : word) m rom) (mkst r1 (0x74e44 : word) m rom)
      /\ bkt = (bv_unsigned h mod 2 ^ 20)%Z
      /\ getr r1 19 = h /\ getr r1 18 = Z_to_bv 64 (DEPOT + 4 * bkt) /\ getr r1 11 = Z_to_bv 64 (tab bkt)
      /\ getr r1 25 = Z_to_bv 64 (tab bkt) /\ getr r1 22 = Z_to_bv 64 65535 /\ getr r1 23 = Z_to_bv 64 2147483647
      /\ getr r1 24 = Z_to_bv 64 MAP1 /\ getr r1 20 = Z_to_bv 64 5854432
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 18 -> r <> 19 -> r <> 20 ->
                    r <> 22 -> r <> 23 -> r <> 24 -> r <> 25 -> getr r1 r = getr regs r).
  Proof.
    intros m regs mul h1 HtabM H9 H13 H10 H12. pose proof Hw as (Ew & Hsz & Htg).
    (* [comment removed for export] *)
    assert (A : exists r0 (h : word),
      msteps SEGS (mkst regs (0x74dd8 : word) m rom) (mkst r0 (0x74e18 : word) m rom)
      /\ getr r0 19 = h /\ getr r0 9 = Z_to_bv 64 DEPOT /\ getr r0 13 = Z_to_bv 64 4194304
      /\ getr r0 22 = Z_to_bv 64 65535 /\ getr r0 23 = Z_to_bv 64 2147483647
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 19 -> r <> 22 -> r <> 23 -> getr r0 r = getr regs r)).
    { eexists _, _. split.
      - ai F_74dd8 D_74dd8. ai F_74ddc D_74ddc. ai F_74de0 D_74de0. ai F_74de4 D_74de4.
        ai F_74de8 D_74de8. ai F_74dec D_74dec. ai F_74df0 D_74df0. ai F_74df4 D_74df4.
        ai F_74df8 D_74df8. ai F_74dfc D_74dfc. ai F_74e00 D_74e00. ai F_74e04 D_74e04.
        ai F_74e08 D_74e08. ai F_74e0c D_74e0c. ai F_74e10 D_74e10. ai F_74e14 D_74e14.
        apply mst_refl.
      - post_regs. }
    destruct A as (r0 & h & RUN0 & Q19 & Q9 & Q13 & Q22 & Q23 & QR).
    pose proof (u64_range h) as Hh.
    set (bkt := (bv_unsigned h mod 2 ^ 20)%Z).
    assert (Hbkt : (0 <= bkt < 2 ^ 20)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
    destruct (HtabM bkt Hbkt) as [[Htc Htr] Htn]. cbn in Htr.
    eexists _, h, bkt. split; [|split; [reflexivity|]].
    - eapply msteps_trans; [exact RUN0|].
      ai F_74e18 D_74e18.
      ai F_74e1c D_74e1c. rewrite bucket_off. fold bkt.
      ai F_74e20 D_74e20.
      ld_step F_74e24 D_74e24 (word_to_le_bytes 4 (Z_to_bv 64 (tab bkt))) (Z_to_bv 64 (tab bkt))
        ltac:(rewrite ?Z.add_0_r; exact Htc)
        ltac:(rewrite bytes_le_cell by (first [cbn; lia | lia]); symmetry; apply u64_lit; lia).
      rewrite v_lw_lit by lia.
      ai F_74e28 D_74e28.
      ai F_74e2c D_74e2c.
      afence F_74e30 D_74e30.
      ai F_74e34 D_74e34. rewrite v_and_lit by lia. change 2147483647%Z with (Z.ones 31). rewrite Z.land_ones, Z.mod_small by (ltac2:(LK.k [@LENBS; @Htr; @HTstk; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @Hsz; @Hh; @Htn]); lia).
      ai F_74e38 D_74e38.
      ai F_74e3c D_74e3c.
      ai F_74e40 D_74e40.
      apply mst_refl.
    - post_regs. all: first [apply QR; assumption | rewrite QR by (intros E; discriminate E); first [reflexivity | assumption]].
  Qed.

  #[using="mem T size bs HTrd LENBS"] Lemma v_srliw_small16 : forall z, (0 <= z < 2 ^ 16)%Z -> v_srliw (Z_to_bv 64 z) 16 = Z_to_bv 64 0.
  Proof.
    intros z Hz. unfold v_srliw. rewrite u64_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="mem usp T w size tag bs P tf st Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma find_loop : forall m (i : nat) regs s (h : word),
    cell64 m MAP1 B ->
    (forall id, (1 <= id <= n)%Z ->
       rdn SEGS m (Z_to_bv 64 (B + 16 * id)) 8 = Some (word_to_le_bytes 8 (hsh id))
       /\ cell32 m (B + 16 * id + 8) (lnk id) /\ (0 <= lnk id < id)%Z) ->
    Z.of_nat i = s -> (0 <= s <= n)%Z ->
    getr regs 11 = Z_to_bv 64 s -> getr regs 24 = Z_to_bv 64 MAP1 -> getr regs 22 = Z_to_bv 64 65535 -> getr regs 19 = h ->
    exists r1 (found : bool),
      msteps SEGS (mkst regs (0x74e44 : word) m rom) (mkst r1 (if found then (0x74f48 : word) else (0x74e9c : word)) m rom)
      /\ (if found then exists id, (1 <= id <= n)%Z /\ getr r1 10 = Z_to_bv 64 id else getr r1 11 = Z_to_bv 64 0)
      /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> getr r1 r = getr regs r).
  Proof.
    intros m i. induction i as [i IH] using lt_wf_ind.
    intros regs s h HmapM HnodesM Hi Hs H11 H24 H22 H19.
    destruct HmapM as [HmapC HBr]. cbn in HBr.
    destruct (Z.eq_dec s 0) as [Hs0|Hs0].
    - (* [comment removed for export] *)
      exists regs, false. split; [|split; [rewrite H11, Hs0; reflexivity | intros; reflexivity]].
      stepb_tk F_74e44 D_74e44 ltac:(pin; rewrite Hs0; reflexivity).
      apply mst_refl.
    - destruct (HnodesM s ltac:(lia)) as (Hhs & [Hlc Hlr] & Hlnk). cbn in Hlr.
      (* [comment removed for export] *)
      assert (PROBE : exists r0,
        msteps SEGS (mkst regs (0x74e44 : word) m rom) (mkst r0 (0x74e7c : word) m rom)
        /\ getr r0 10 = Z_to_bv 64 s /\ getr r0 12 = hsh s /\ getr r0 11 = Z_to_bv 64 (lnk s)
        /\ getr r0 24 = Z_to_bv 64 MAP1 /\ getr r0 22 = Z_to_bv 64 65535 /\ getr r0 19 = h
        /\ (forall r, r <> 10 -> r <> 11 -> r <> 12 -> getr r0 r = getr regs r)).
      { eexists. split.
        - stepb_ft F_74e44 D_74e44 ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
          ai F_74e48 D_74e48. rewrite ?Z.add_0_r.
          ai F_74e4c D_74e4c. rewrite v_srliw_small16 by lia.
          ai F_74e50 D_74e50.
          ai F_74e54 D_74e54. rewrite ?Z.add_0_r.
          ld_step F_74e58 D_74e58 (word_to_le_bytes 8 (Z_to_bv 64 B)) (Z_to_bv 64 B)
            ltac:(rewrite ?Z.add_0_r; exact HmapC) ltac:(apply bytes_le_to_Z_8).
          stepb_ft F_74e5c D_74e5c ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
          ai F_74e60 D_74e60. rewrite v_slli_lit by (try lia; change (2 ^ 32)%Z with 4294967296%Z; lia).
          ai F_74e64 D_74e64. rewrite v_srli_lit by (change (2 ^ 32)%Z with 4294967296%Z; (ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @HBr; @Hs; @Hs0; @Hlr; @Hlnk]); lia)). rewrite Z.div_mul by lia.
          ai F_74e68 D_74e68. rewrite v_and_lit by lia. change 65535%Z with (Z.ones 16). rewrite Z.land_ones, Z.mod_small by lia.
          ai F_74e6c D_74e6c. rewrite v_slli_lit by lia.
          ai F_74e70 D_74e70.
          ld_step F_74e74 D_74e74 (word_to_le_bytes 8 (hsh s)) (hsh s)
            ltac:(rewrite ?Z.add_0_r; replace (B + s * 2 ^ 4)%Z with (B + 16 * s)%Z by lia; exact Hhs) ltac:(apply bytes_le_to_Z_8).
          ld_step F_74e78 D_74e78 (word_to_le_bytes 4 (Z_to_bv 64 (lnk s))) (Z_to_bv 64 (lnk s))
            ltac:(replace (B + s * 2 ^ 4 + 8)%Z with (B + 16 * s + 8)%Z by (ltac2:(LK.k [@Husp; @HT; @Hw; @Hn; @HB; @HTP; @LENBS; @HBr; @Hs; @Hs0; @Hlr; @HTstk; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @Hlnk]); lia); exact Hlc)
            ltac:(rewrite bytes_le_cell by (first [cbn; (ltac2:(LK.k [@Husp; @HT; @Hw; @Hn; @HB; @HTP; @LENBS; @HBr; @Hs; @Hs0; @Hlr; @HTstk; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @Hlnk]); lia) | (ltac2:(LK.k [@Husp; @HT; @Hw; @Hn; @HB; @HTP; @LENBS; @HBr; @Hs; @Hs0; @Hlr; @HTstk; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @Hlnk]); lia)]); symmetry; apply u64_lit; (ltac2:(LK.k [@Husp; @HT; @Hw; @Hn; @HB; @HTP; @LENBS; @HBr; @Hs; @Hs0; @Hlr; @HTstk; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @Hlnk]); lia)).
          rewrite v_lw_lit by lia.
          apply mst_refl.
        - post_regs. }
      destruct PROBE as (r0 & RUN0 & Q10 & Q12 & Q11 & Q24 & Q22 & Q19 & QR).
      destruct (c_eq h (hsh s)) eqn:E.
      + (* [comment removed for export] *)
        exists r0, true. split; [|split; [exists s; split; [lia | exact Q10] | exact QR]].
        eapply msteps_trans; [exact RUN0|].
        stepb_ft F_74e7c D_74e7c ltac:(pin; exact E).
        stepj F_74e80 D_74e80.
        apply mst_refl.
      + (* [comment removed for export] *)
        destruct (IH (Z.to_nat (lnk s)) ltac:((ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @HBr; @Hi; @Hs; @Hs0; @Hlr; @Hlnk; @E; @HB]); lia)) r0 (lnk s) h) as (r1 & found & RUN1 & P1 & PR);
          [split; [exact HmapC | cbn; (ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @HBr; @Hi; @Hs; @Hs0; @Hlr; @Hlnk; @E; @HB]); lia)] | exact HnodesM | (ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @HBr; @Hi; @Hs; @Hs0; @Hlr; @Hlnk; @E; @HB]); lia) | (ltac2:(LK.k [@HTstk; @Hw; @Hn; @HBstk; @HBT; @HBP; @HPstk; @HTP; @LENBS; @HBr; @Hi; @Hs; @Hs0; @Hlr; @Hlnk; @E; @HB]); lia) | exact Q11 | exact Q24 | exact Q22 | exact Q19 |].
        exists r1, found. split; [|split; [exact P1 | intros r N10 N11 N12; rewrite PR by assumption; apply QR; assumption]].
        eapply msteps_trans; [exact RUN0|].
        stepb_tk F_74e7c D_74e7c ltac:(pin; rewrite E; reflexivity).
        exact RUN1.
  Qed.

  (* [comment removed for export] *)
  #[using="mem T size bs Husp HTrd Hret LENBS"] Lemma put_epi : forall M regs (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word),
    getr regs 2 = Z_to_bv 64 (usp - 112) ->
    rdn SEGS M (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS M (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    rdn SEGS M (Z_to_bv 64 (usp - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS M (Z_to_bv 64 (usp - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
    rdn SEGS M (Z_to_bv 64 (usp - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
    exists r1,
      msteps SEGS (mkst regs (0x74f48 : word) M rom) (mkst r1 ret M rom)
      /\ getr r1 2 = Z_to_bv 64 usp /\ getr r1 1 = ret /\ getr r1 8 = v8 /\ getr r1 9 = v9
      /\ getr r1 18 = v18 /\ getr r1 19 = v19 /\ getr r1 20 = v20 /\ getr r1 21 = v21
      /\ getr r1 22 = v22 /\ getr r1 23 = v23 /\ getr r1 24 = v24 /\ getr r1 25 = v25
      /\ (forall r, r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 -> r <> 22 -> r <> 23 ->
                    r <> 24 -> r <> 25 -> getr r1 r = getr regs r).
  Proof.
    intros M regs v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 H2 R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25.
    Local Ltac eld F D vv R := ld_step F D (word_to_le_bytes 8 vv) vv
      ltac:(match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => match type of R with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia end end; exact R) ltac:(apply bytes_le_to_Z_8).
    eexists. split.
    - eld F_74f48 D_74f48 ret R1.
      eld F_74f4c D_74f4c v8 R8.
      eld F_74f50 D_74f50 v9 R9.
      eld F_74f54 D_74f54 v18 R18.
      eld F_74f58 D_74f58 v19 R19.
      eld F_74f5c D_74f5c v20 R20.
      eld F_74f60 D_74f60 v21 R21.
      eld F_74f64 D_74f64 v22 R22.
      eld F_74f68 D_74f68 v23 R23.
      eld F_74f6c D_74f6c v24 R24.
      eld F_74f70 D_74f70 v25 R25.
      ai F_74f74 D_74f74. replace (usp - 112 + 112)%Z with usp by lia.
      stepjr F_74f78 D_74f78 ret ltac:(gr; pin; first [reflexivity | assumption]). imm_norm. rewrite (Hret : v_jalr ret 0 = ret).
      apply mst_refl.
    - post_regs.
  Qed.


  (* [comment removed for export] *)
  Definition ins_mem (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) (bkt : Z) : word -> option byte :=
    let t := tab bkt in let p := (DEPOT + 4 * bkt)%Z in let N := (B + 16 * (n + 1))%Z in
    let m0 := put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 in
    let m1 := lock_mem m0 (usp - 112) p t (0x74ea4 : word) (Z_to_bv 64 0) (Z_to_bv 64 DEPOT) (Z_to_bv 64 p) h in
    let m2 := wbytes m1 (Z_to_bv 64 NIDS) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1))) in
    let m3 := ns_mem m2 (usp - 112) N tf P st size tag h bs (0x74f2c : word)
                     (Z_to_bv 64 0) (Z_to_bv 64 N) (Z_to_bv 64 p) h (Z_to_bv 64 5854432) (Z_to_bv 64 t) in
    let m4 := wbytes m3 (Z_to_bv 64 (N + 8)) (word_to_le_bytes 4 (Z_to_bv 64 t)) in
    wbytes m4 (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1))).

  Ltac unfm := unfold ins_mem, ns_mem, ss_mem, alloc_mem, ss_mem1, ns_mem1, lock_mem, lock_frame, put_frame.

  (* [comment removed for export] *)
  #[using="Husp Hstk HT HTrd HTstk Hw Hn Htab Hnid Hmap HB Hnew HBstk HBT HBP Htf HP Hst Hroom HPblk HPok HPstk HTP LENBS"] Lemma put_ins : forall regs (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt,
    (0 <= bkt < 2 ^ 20)%Z ->
    getr regs 2 = Z_to_bv 64 (usp - 112) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 DEPOT ->
    getr regs 18 = Z_to_bv 64 (DEPOT + 4 * bkt) -> getr regs 19 = h -> getr regs 20 = Z_to_bv 64 5854432 ->
    getr regs 22 = Z_to_bv 64 65535 -> getr regs 24 = Z_to_bv 64 MAP1 -> getr regs 25 = Z_to_bv 64 (tab bkt) ->
    exists r1,
      msteps SEGS (mkst regs (0x74e9c : word) (put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25) rom)
                  (mkst r1 (0x74f48 : word) (ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt) rom)
      /\ getr r1 10 = Z_to_bv 64 (n + 1) /\ getr r1 2 = Z_to_bv 64 (usp - 112)
      /\ (forall r, r <> 1 -> r <> 5 -> r <> 6 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 ->
                    r <> 21 -> r <> 23 -> getr r1 r = getr regs r).
  Proof.
    intros regs v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt Hbkt H2 H8 H9 H18 H19 H20 H22 H24 H25. hide_disjs.
    pose proof Hw as (Ew & Hsz & Htg). pose proof Htf as [Htfc Htfr]. pose proof HP as [HPc HPr]. pose proof Hst as [Hstc Hstr].
    pose proof Hnid as [Hnc Hnr]. pose proof Hmap as [Hmc Hmr]. cbn in Htfr, HPr, Hstr, Hnr, Hmr.
    destruct (Htab bkt Hbkt) as [[Htc Htr] Htn]. cbn in Htr.
    set (t := tab bkt) in *. set (p := (DEPOT + 4 * bkt)%Z) in *.
    assert (Hp4 : (p mod 4 = 0)%Z) by (unfold p; apply (proj2 (Z.mod_divide _ 4 ltac:(lia))); exists (415030 + bkt)%Z; lia).
    set (m0 := put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25).
    (* [comment removed for export] *)
    assert (SA : exists ra,
      msteps SEGS (mkst regs (0x74e9c : word) m0 rom) (mkst ra (0x75498 : word) m0 rom)
      /\ getr ra 1 = (0x74ea4 : word) /\ getr ra 2 = Z_to_bv 64 (usp - 112) /\ getr ra 10 = Z_to_bv 64 p
      /\ (forall r, r <> 1 -> r <> 10 -> getr ra r = getr regs r)).
    { eexists. split.
      - ai F_74e9c D_74e9c. stepj F_74ea0 D_74ea0. apply mst_refl.
      - post_regs. }
    destruct SA as (ra & RUNA & A1 & A2 & A10 & AR).
    destruct (lock_walk m0 rom (usp - 112) p t (0x74ea4 : word)) with (regs := ra)
      as (rb & RUNB & B10 & B2 & B1 & BR); try assumption.
    { lia. }
    { unfold m0, put_frame. repeat apply okr_wbytes. eapply okr_sub; [exact Hstk | lia | lia]. }
    { split; [|split]; [unfold p; lia | unfold p; lia | exact Hp4]. }
    { split; [unfold m0, put_frame; peelp; exact Htc | cbn; (ltac2:(LK.k [@LENBS; @Hbkt; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Husp; @Htn]); lia)]. }
    { lia. }
    { unfold m0, put_frame. repeat apply okr_wbytes. apply okr_rw; unfold p; lia. }
    { unfold p. lia. }
    { apply ret_ok_even; vm_compute; reflexivity. }
    rewrite A1, (AR 8), (AR 9), (AR 18), (AR 19), H8, H9, H18, H19 in RUNB by (intros E; discriminate E).
    fold p in RUNB.
    set (m1 := lock_mem m0 (usp - 112) p t (0x74ea4 : word) (Z_to_bv 64 0) (Z_to_bv 64 DEPOT) (Z_to_bv 64 p) h) in RUNB.
    assert (B9 : getr rb 9 = Z_to_bv 64 DEPOT) by (rewrite BR, AR by (intros E; discriminate E); exact H9).
    assert (B25 : getr rb 25 = Z_to_bv 64 t) by (rewrite BR, AR by (intros E; discriminate E); exact H25).
    assert (B24 : getr rb 24 = Z_to_bv 64 MAP1) by (rewrite BR, AR by (intros E; discriminate E); exact H24).
    assert (B22 : getr rb 22 = Z_to_bv 64 65535) by (rewrite BR, AR by (intros E; discriminate E); exact H22).
    assert (B19 : getr rb 19 = h) by (rewrite BR, AR by (intros E; discriminate E); exact H19).
    (* [comment removed for export] *)
    assert (SC : exists rc,
      msteps SEGS (mkst rb (0x74ea4 : word) m1 rom)
                  (mkst rc (0x74a1c : word) (wbytes m1 (Z_to_bv 64 NIDS) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) rom)
      /\ getr rc 1 = (0x74f2c : word) /\ getr rc 2 = Z_to_bv 64 (usp - 112) /\ getr rc 10 = Z_to_bv 64 (B + 16 * (n + 1))
      /\ getr rc 12 = Z_to_bv 64 (usp - 112 + 8) /\ getr rc 13 = h
      /\ getr rc 9 = Z_to_bv 64 (B + 16 * (n + 1)) /\ getr rc 21 = Z_to_bv 64 t /\ getr rc 23 = Z_to_bv 64 (n + 1)
      /\ (forall r, r <> 1 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 21 -> r <> 23 -> getr rc r = getr rb r)).
    { eexists. split.
      - ai F_74ea4 D_74ea4.
        stepb_tk F_74ea8 D_74ea8 ltac:(pin; unfold c_eq; apply bv_eqb_refl).
        ai F_74ed4 D_74ed4.
        ai F_74ed8 D_74ed8.
        ai F_74edc D_74edc.
        chain_step; [reflexivity
          | eapply (step_amoadd_w _ _ _ rom _ _ _ 10 10 11 NIDS n);
            [ exact F_74ee0 | reflexivity | exact D_74ee0 | gr; pin; reflexivity | (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia) | (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia) | reflexivity
            | split; [unfold m1, m0, lock_mem, lock_frame, put_frame; peelp; exact Hnc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia)] | (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia)
            | apply okr_store_ok; [(ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia) | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia) | repeat apply okr_wbytes; apply okr_rw; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Husp; @Hn]); lia)] ]
          | step_simpl ].
        nz. change (bv_unsigned (Z_to_bv 64 1)) with 1%Z. rewrite (Z.mod_small (n + 1)) by lia.
        ai F_74ee4 D_74ee4. rewrite v_addiw_lit by lia.
        ai F_74ee8 D_74ee8. rewrite v_slli_lit by (try lia; change (2 ^ 32)%Z with 4294967296%Z; lia).
        ai F_74eec D_74eec. rewrite v_srli_lit by (change (2 ^ 32)%Z with 4294967296%Z; lia). rewrite Z.div_mul by lia.
        stepb_ft F_74ef0 D_74ef0 ltac:(pin; rewrite c_lts_zbv by lia; apply Z.ltb_ge; lia).
        ai F_74ef4 D_74ef4.
        ai F_74ef8 D_74ef8. rewrite v_srli_lit, Z.div_small by lia.
        ai F_74efc D_74efc.
        ai F_74f00 D_74f00.
        ld_step F_74f04 D_74f04 (word_to_le_bytes 8 (Z_to_bv 64 B)) (Z_to_bv 64 B)
          ltac:(unfold m1, m0, lock_mem, lock_frame, put_frame; peelp; exact Hmc) ltac:(apply bytes_le_to_Z_8).
        stepb_ft F_74f08 D_74f08 ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
        ai F_74f0c D_74f0c. rewrite v_and_lit by lia. change 65535%Z with (Z.ones 16). rewrite Z.land_ones, Z.mod_small by lia.
        ai F_74f10 D_74f10. rewrite v_slli_lit by lia.
        ai F_74f14 D_74f14.
        ai F_74f18 D_74f18.
        ai F_74f1c D_74f1c.
        ai F_74f20 D_74f20.
        ai F_74f24 D_74f24.
        stepj F_74f28 D_74f28.
        replace ((n + 1) * 2 ^ 4)%Z with (16 * (n + 1))%Z by lia.
        apply mst_refl.
      - post_regs. }
    destruct SC as (rc & RUNC & C1 & C2 & C10 & C12 & C13 & C9 & C21 & C23 & CR).
    set (N := (B + 16 * (n + 1))%Z) in *.
    set (m2 := wbytes m1 _ _) in RUNC.
    destruct (nstore_walk m2 rom (usp - 112) N tf P st T w size tag h bs (0x74f2c : word)) with (regs := rc)
      as (rd & RUND & D2 & D1 & DR); try assumption.
    { lia. }
    { unfold m2, m1, m0; unfm. repeat apply okr_wbytes. eapply okr_sub; [exact Hstk | lia | lia]. }
    { split; [unfold m2, m1, m0; unfm; peelp; hit8 | cbn; (ltac2:(LK.k [@Husp; @LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @HT; @Ew; @Hsz]); lia)]. }
    { split; [unfold m2, m1, m0; unfm; peelp; hit8 | cbn; rewrite Ew; (ltac2:(LK.k [@Husp; @LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Hsz; @Htg]); lia)]. }
    { split; [unfold m2, m1, m0; unfm; peelp; exact Htfc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Husp; @Hroom]); lia)]. }
    { split; [unfold m2, m1, m0; unfm; peelp; exact HPc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Husp; @HPblk]); lia)]. }
    { split; [unfold m2, m1, m0; unfm; peelp; exact Hstc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Hstr; @Hnr; @Hmr; @Htr; @Hbkt; @Husp; @Hroom]); lia)]. }
    { unfold m2, m1, m0; unfm. repeat apply okr_wbytes. exact HPok. }
    { unhide HTstk. unfold m2, m1, m0; unfm. peelp. exact HTrd. }
    { unhide HTstk. lia. }
    { unhide HPstk. lia. }
    { unfold N. lia. }
    { unfold m2, m1, m0; unfm. repeat apply okr_wbytes. exact Hnew. }
    { unhide HBstk. unfold N. lia. }
    { unhide HBT. unfold N. lia. }
    { unhide HBP. unfold N. lia. }
    { apply ret_ok_even; vm_compute; reflexivity. }
    rewrite (CR 8), (BR 8), (AR 8), H8, C9, (CR 18), (BR 18), (AR 18), H18, (CR 19), B19, (CR 20), (BR 20), (AR 20), H20, C21 in RUND
      by (intros E; discriminate E).
    set (m3 := ns_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in RUND.
    assert (D9 : getr rd 9 = Z_to_bv 64 N) by (rewrite DR by (intros E; discriminate E); exact C9).
    assert (D21 : getr rd 21 = Z_to_bv 64 t) by (rewrite DR by (intros E; discriminate E); exact C21).
    assert (D23 : getr rd 23 = Z_to_bv 64 (n + 1)) by (rewrite DR by (intros E; discriminate E); exact C23).
    assert (D18 : getr rd 18 = Z_to_bv 64 p) by (rewrite DR, CR, BR, AR by (intros E; discriminate E); exact H18).
    assert (D8 : getr rd 8 = Z_to_bv 64 0) by (rewrite DR, CR, BR, AR by (intros E; discriminate E); exact H8).
    (* [comment removed for export] *)
    eexists. split; [|split; [|split]].
    - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|].
      eapply msteps_trans; [exact RUNC|]. eapply msteps_trans; [exact RUND|].
      ast F_74f2c D_74f2c (Z_to_bv 64 (N + 8)) (Z_to_bv 64 t)
        ltac:(unfold m3, m2, m1, m0; unfm; apply okr_store_ok; [lia | cbn; lia | repeat apply okr_wbytes; eapply okr_sub; [exact Hnew | unfold N; lia | unfold N; lia] ]).
      afence F_74f30 D_74f30.
      ai F_74f34 D_74f34.
      ast F_74f38 D_74f38 (Z_to_bv 64 p) (Z_to_bv 64 (n + 1))
        ltac:(unfold m3, m2, m1, m0; unfm; apply okr_store_ok; [lia | cbn; lia | repeat apply okr_wbytes; apply okr_rw; unfold p; lia]).
      stepb_tk F_74f3c D_74f3c ltac:(pin; reflexivity).
      unfold m3, m2, m1, m0, ins_mem. fold t p N. apply mst_refl.
    - gr. reflexivity.
    - gr. exact D2.
    - intros r; intros. repeat (rewrite getr_other by assumption).
      rewrite DR, CR, BR, AR by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma ins_mem_frame : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt (x : word),
    (0 <= bkt < 2 ^ 20)%Z -> (usp - 112 <= bv_unsigned x < usp)%Z ->
    ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt x = put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 x.
  Proof.
    intros v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt x Hbkt Hx. pose proof Hw as (Ew & Hsz & Htg).
    unfold ins_mem, ns_mem, ss_mem, alloc_mem, ss_mem1, ns_mem1, lock_mem, lock_frame.
    repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?LENBS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; (ltac2:(LK.k [@LENBS; @Hbkt; @Husp; @Hx; @HT; @Hn; @HB; @HTP; @Hsz; @HTstk; @HBstk; @HBT; @HBP; @Hroom; @HPblk; @HPstk]); lia))).
    reflexivity.
  Qed.

  #[using="Husp HT HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma ins_mem_slot : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt a,
    (0 <= bkt < 2 ^ 20)%Z -> (usp - 112 <= a)%Z -> (a + 8 <= usp)%Z ->
    rdn SEGS (ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt) (Z_to_bv 64 a) 8
    = rdn SEGS (put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25) (Z_to_bv 64 a) 8.
  Proof.
    intros. apply rdn_ext; [unorm; (ltac2:(LK.k [@Husp; @LENBS; @H0; @Hw; @HB; @HBstk; @HBP; @Hroom; @HPblk; @HPstk; @HTP; @H1]); lia)|]. intros x Hx. rewrite u64_lit in Hx by lia. apply ins_mem_frame; [assumption | lia].
  Qed.

  Ltac slotPF := unfold put_frame; peelp; hit8.

  (* [comment removed for export] *)
  #[using="lnk hsh Husp Hstk HT HTrd HTstk Hw Hn Htab Hnid Hmap HB Hnodes Hnew HBstk HBT HBP Htf HP Hst Hroom HPblk HPok HPstk HTP Hret LENBS"] Theorem put_walk : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 T -> getr regs 11 = Z_to_bv 64 w ->
    exists r' (h : word) (found : bool),
      msteps SEGS (mkst regs (0x74d04 : word) mem rom)
                  (mkst r' ret (if found then PF regs
                                else ins_mem (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                                             (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) h (bv_unsigned h mod 2 ^ 20)) rom)
      /\ (if found then exists id, (1 <= id <= n)%Z /\ getr r' 10 = Z_to_bv 64 id else getr r' 10 = Z_to_bv 64 (n + 1))
      /\ getr r' 2 = Z_to_bv 64 usp /\ getr r' 1 = ret
      /\ (forall r, r <> 5 -> r <> 6 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 ->
                    getr r' r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11. hide_disjs. pose proof Hw as (Ew & Hsz & Htg). pose proof Hmap as [Hmc Hmr]. cbn in Hmr.
    destruct (put_pro regs H1 H2 H10 H11) as (r1 & RUN1 & P2 & P8 & P9 & P11 & P12 & P13 & PR).
    set (m0 := PF regs) in *.
    assert (HTrd0 : rdn SEGS m0 (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs) by (unhide HTstk; unfold m0, put_frame; peelp; exact HTrd).
    destruct (hash_pre m0 r1 P11 P12) as (r2 & mul & h0 & RUN2 & Q11 & Q14 & Q13 & Q10 & Q12 & QR).
    destruct (hash_loop m0 (Z.to_nat (size - 1)) r2 0 mul HTrd0) as (r3 & h1 & RUN3 & S12 & S10 & SR);
      [rewrite Q11; f_equal; lia | exact Q14 | exact Q10 | lia | lia |].
    assert (Htab0 : forall b, (0 <= b < 2 ^ 20)%Z -> cell32 m0 (DEPOT + 4 * b) (tab b) /\ (0 <= tab b <= n)%Z).
    { intros b Hb. destruct (Htab b Hb) as [[Hc Hr] Hbn]. split; [split; [unfold m0, put_frame; peelp; exact Hc | exact Hr] | exact Hbn]. }
    assert (S9 : getr r3 9 = Z_to_bv 64 DEPOT) by (rewrite SR, QR by (intros E; discriminate E); exact P9).
    assert (S13 : getr r3 13 = Z_to_bv 64 tag) by (rewrite SR by (intros E; discriminate E); exact Q13).
    destruct (hash_fin m0 r3 mul h1 Htab0 S9 S13 S10 S12) as (r4 & h & bkt & RUN4 & Hbkt & F19 & F18 & F11 & F25 & F22 & F23 & F24 & F20 & FR).
    pose proof (u64_range h) as Hh.
    assert (Hbk : (0 <= bkt < 2 ^ 20)%Z) by (rewrite Hbkt; apply Z.mod_pos_bound; lia).
    destruct (Htab bkt Hbk) as [_ Htn].
    assert (Hnodes0 : forall id, (1 <= id <= n)%Z ->
       rdn SEGS m0 (Z_to_bv 64 (B + 16 * id)) 8 = Some (word_to_le_bytes 8 (hsh id))
       /\ cell32 m0 (B + 16 * id + 8) (lnk id) /\ (0 <= lnk id < id)%Z).
    { unhide HBstk. intros id Hid. destruct (Hnodes id Hid) as (Ha & [Hb Hbr] & Hc).
      split; [unfold m0, put_frame; peelp; exact Ha|]. split; [split; [unfold m0, put_frame; peelp; exact Hb | exact Hbr] | exact Hc]. }
    destruct (find_loop m0 (Z.to_nat (tab bkt)) r4 (tab bkt) h) as (r5 & found & RUN5 & F5 & R5);
      [split; [unfold m0, put_frame; peelp; exact Hmc | cbn; (ltac2:(LK.k [@LENBS; @Hmr; @Husp; @HB; @Hsz; @Hh; @Htn]); lia)] | exact Hnodes0 | (ltac2:(LK.k [@LENBS; @Hmr; @Husp; @HB; @Hsz; @Hh; @Htn]); lia) | (ltac2:(LK.k [@LENBS; @Hmr; @Husp; @HB; @Hsz; @Hh; @Htn]); lia) | exact F11 | exact F24 | exact F22 | exact F19 |].
    assert (E2 : getr r5 2 = Z_to_bv 64 (usp - 112)) by (rewrite R5, FR, SR, QR by (intros E; discriminate E); exact P2).
    (* [comment removed for export] *)
    assert (KEEP : forall r, r <> 2 -> r <> 8 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> r <> 16 ->
                   r <> 18 -> r <> 19 -> r <> 20 -> r <> 22 -> r <> 23 -> r <> 24 -> r <> 25 -> getr r5 r = getr regs r).
    { intros. rewrite R5, FR, SR, QR, PR by assumption. reflexivity. }
    destruct found.
    - (* [comment removed for export] *)
      destruct (put_epi m0 r5 (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) E2)
        as (r6 & RUN6 & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & GR);
        [unfold m0; slotPF .. |].
      exists r6, h, true. split; [|split; [|split; [exact G2 | split; [exact G1|]]]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
        eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
      + destruct F5 as (id & Hid & A10). exists id. split; [exact Hid|]. rewrite GR by (intros E; discriminate E). exact A10.
      + intros r N5 N6 N10 N11 N12 N13 N14 N15 N16.
        destruct (bv_eq_dec 5 r 1) as [->|N1]; [rewrite G1; symmetry; exact H1|].
        destruct (bv_eq_dec 5 r 2) as [->|N2]; [rewrite G2; symmetry; exact H2|].
        destruct (bv_eq_dec 5 r 8) as [->|N8]; [exact G8|]. destruct (bv_eq_dec 5 r 9) as [->|N9]; [exact G9|].
        destruct (bv_eq_dec 5 r 18) as [->|N18]; [exact G18|]. destruct (bv_eq_dec 5 r 19) as [->|N19]; [exact G19|].
        destruct (bv_eq_dec 5 r 20) as [->|N20]; [exact G20|]. destruct (bv_eq_dec 5 r 21) as [->|N21]; [exact G21|].
        destruct (bv_eq_dec 5 r 22) as [->|N22]; [exact G22|]. destruct (bv_eq_dec 5 r 23) as [->|N23]; [exact G23|].
        destruct (bv_eq_dec 5 r 24) as [->|N24]; [exact G24|]. destruct (bv_eq_dec 5 r 25) as [->|N25]; [exact G25|].
        rewrite GR by assumption. apply KEEP; assumption.
    - (* [comment removed for export] *)
      assert (E8 : getr r5 8 = Z_to_bv 64 0) by (rewrite R5, FR, SR, QR by (intros E; discriminate E); exact P8).
      assert (E9 : getr r5 9 = Z_to_bv 64 DEPOT) by (rewrite R5, FR by (intros E; discriminate E); exact S9).
      assert (E18 : getr r5 18 = Z_to_bv 64 (DEPOT + 4 * bkt)) by (rewrite R5 by (intros E; discriminate E); exact F18).
      assert (E19 : getr r5 19 = h) by (rewrite R5 by (intros E; discriminate E); exact F19).
      assert (E20 : getr r5 20 = Z_to_bv 64 5854432) by (rewrite R5 by (intros E; discriminate E); exact F20).
      assert (E22 : getr r5 22 = Z_to_bv 64 65535) by (rewrite R5 by (intros E; discriminate E); exact F22).
      assert (E24 : getr r5 24 = Z_to_bv 64 MAP1) by (rewrite R5 by (intros E; discriminate E); exact F24).
      assert (E25 : getr r5 25 = Z_to_bv 64 (tab bkt)) by (rewrite R5 by (intros E; discriminate E); exact F25).
      destruct (put_ins r5 (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) h bkt Hbk E2 E8 E9 E18 E19 E20 E22 E24 E25)
        as (r6 & RUN6 & I10 & I2 & IR).
      destruct (put_epi (ins_mem (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                                 (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) h bkt)
                        r6 (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                        (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) I2)
        as (r7 & RUN7 & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & GR);
        [rewrite ins_mem_slot by (ltac2:(LK.k [@LENBS; @Hmr; @Hbk; @Husp]); lia); slotPF .. |].
      exists r7, h, false. rewrite <- Hbkt. split; [|split; [|split; [exact G2 | split; [exact G1|]]]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
        eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. exact RUN7.
      + rewrite GR by (intros E; discriminate E). exact I10.
      + intros r N5 N6 N10 N11 N12 N13 N14 N15 N16.
        destruct (bv_eq_dec 5 r 1) as [->|N1]; [rewrite G1; symmetry; exact H1|].
        destruct (bv_eq_dec 5 r 2) as [->|N2]; [rewrite G2; symmetry; exact H2|].
        destruct (bv_eq_dec 5 r 8) as [->|N8]; [exact G8|]. destruct (bv_eq_dec 5 r 9) as [->|N9]; [exact G9|].
        destruct (bv_eq_dec 5 r 18) as [->|N18]; [exact G18|]. destruct (bv_eq_dec 5 r 19) as [->|N19]; [exact G19|].
        destruct (bv_eq_dec 5 r 20) as [->|N20]; [exact G20|]. destruct (bv_eq_dec 5 r 21) as [->|N21]; [exact G21|].
        destruct (bv_eq_dec 5 r 22) as [->|N22]; [exact G22|]. destruct (bv_eq_dec 5 r 23) as [->|N23]; [exact G23|].
        destruct (bv_eq_dec 5 r 24) as [->|N24]; [exact G24|]. destruct (bv_eq_dec 5 r 25) as [->|N25]; [exact G25|].
        rewrite GR by assumption. rewrite IR by assumption. apply KEEP; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac outs := repeat (rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?LENBS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).

  #[using="size bs Husp HTrd LENBS"] Lemma pf_out : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 x : word),
    (bv_unsigned x < usp - 112 \/ usp <= bv_unsigned x)%Z ->
    put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 x = mem x.
  Proof. intros. unfold put_frame. outs. reflexivity. Qed.

  #[using="Type"] Lemma pf_grows : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word),
    mem_grows mem (put_frame ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25).
  Proof. intros. unfold put_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Definition ins_written (bkt x : Z) : Prop :=
       (usp - 224 <= x < usp)%Z
    \/ (DEPOT + 4 * bkt <= x < DEPOT + 4 * bkt + 4)%Z
    \/ (NIDS <= x < NIDS + 4)%Z
    \/ (B + 16 * (n + 1) <= x < B + 16 * (n + 1) + 16)%Z
    \/ (SSB <= x < SSB + 8)%Z
    \/ (SSB + 24 <= x < SSB + 28)%Z
    \/ (P + 8 * tf <= x < P + 8 * tf + 8 * (size + 1))%Z.

  #[using="Husp HTrd Hw Hn HB Hroom HPblk LENBS"] Lemma ins_out : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt (x : word),
    (0 <= bkt < 2 ^ 20)%Z -> ~ ins_written bkt (bv_unsigned x) ->
    ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt x = mem x.
  Proof.
    intros v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt x Hbkt Hx. pose proof Hw as (Ew & Hsz & Htg).
    unfold ins_written in Hx. pose proof (u64_range x).
    assert (A1 : hideP (bv_unsigned x < usp - 224 \/ usp <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A2 : hideP (bv_unsigned x < DEPOT + 4 * bkt \/ DEPOT + 4 * bkt + 4 <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A3 : hideP (bv_unsigned x < NIDS \/ NIDS + 4 <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A4 : hideP (bv_unsigned x < B + 16 * (n + 1) \/ B + 16 * (n + 1) + 16 <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A5 : hideP (bv_unsigned x < SSB \/ SSB + 8 <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A6 : hideP (bv_unsigned x < SSB + 24 \/ SSB + 28 <= bv_unsigned x)%Z) by (unfold hideP; lia).
    assert (A7 : hideP (bv_unsigned x < P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= bv_unsigned x)%Z) by (unfold hideP; lia).
    clear Hx. hide_disjs. unfm.
    Local Ltac o H := rewrite wbytes_outside by (unhide H; rewrite ?length_N_to_le_bytes, ?LENBS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia).
    o A2. o A4. o A4. o A1. o A6. o A7. o A7. o A1. o A5. o A1. o A1.
    do 9 (o A1).
    o A1. o A4. o A1. o A1.
    o A3.
    o A2. do 5 (o A1).
    do 13 (o A1).
    reflexivity.
  Qed.

  #[using="Type"] Lemma ins_grows : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt,
    mem_grows mem (ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt).
  Proof. intros. unfm. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  #[using="Husp HTrd HTstk Hw Hn HB HBstk HBT HBP Hroom HPblk HPstk HTP LENBS"] Lemma ins_rdn_same : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt a (j : nat),
    (0 <= bkt < 2 ^ 20)%Z -> (0 <= a)%Z -> (a + Z.of_nat j < 2 ^ 64)%Z ->
    (forall x, (a <= x < a + Z.of_nat j)%Z -> ~ ins_written bkt x) ->
    rdn SEGS (ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt) (Z_to_bv 64 a) j = rdn SEGS mem (Z_to_bv 64 a) j.
  Proof.
    intros v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt a j Hbkt Ha Hj Hout.
    apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    apply ins_out; [exact Hbkt | apply Hout; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Definition d0 : dstate := DS n tf st tab lnk hsh.
  Definition d_ins (h : word) (bkt : Z) : dstate :=
    DS (n + 1) (tf + size + 1) (st + size + 1)
       (fun b => if (b =? bkt)%Z then (n + 1)%Z else tab b)
       (fun i => if (i =? n + 1)%Z then tab bkt else lnk i)
       (fun i => if (i =? n + 1)%Z then h else hsh i).

  #[using="T size bs HTrd Hn Htab Hnid Hmap Hnodes Htf HP Hst Hroom LENBS"] Lemma d0_cells : depot_cells B P d0 mem.
  Proof.
    pose proof Hst as [Hstc Hstr]. cbn in Hstr.
    split; [exact Htab|]. split; [exact Hnid|]. split; [exact Hmap|]. split; [exact Hnodes|].
    split; [exact Htf|]. split; [exact HP|]. split; [exact Hst|]. cbn. lia.
  Qed.

  Ltac hit4 :=
    lazymatch goal with |- rdn _ (wbytes _ ?a' (word_to_le_bytes 4 ?v')) ?a 4 = Some (word_to_le_bytes 4 ?v) =>
      (tryif constr_eq a a' then idtac else replace a with a' by (f_equal; lia));
      (tryif constr_eq v v' then idtac else replace v with v' by (first [congruence | f_equal; lia])) end;
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 4 _)); rewrite length_N_to_le_bytes; unorm; lia.

  #[using="Husp HT HTrd HTstk Hw Hn Htab Hnid Hmap HB Hnodes HBstk HBT HBP Htf HP Hst Hroom HPblk HPstk HTP LENBS"] Lemma ins_cells : forall (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h : word) bkt,
    (0 <= bkt < 2 ^ 20)%Z ->
    depot_cells B P (d_ins h bkt) (ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt).
  Proof.
    intros v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt Hbkt. hide_disjs. pose proof Hw as (Ew & Hsz & Htg).
    pose proof Htf as [Htfc Htfr]. pose proof HP as [HPc HPr]. pose proof Hst as [Hstc Hstr].
    pose proof Hnid as [Hnc Hnr]. pose proof Hmap as [Hmc Hmr]. cbn in Htfr, HPr, Hstr, Hnr, Hmr.
    destruct (Htab bkt Hbkt) as [[Htc Htr] Htn]. cbn in Htr.
    set (M := ins_mem v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 h bkt).
    unfold depot_cells, d_ins; cbn [d_n d_tf d_st d_tab d_lnk d_hsh].
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    - (* [comment removed for export] *)
      intros b Hb. destruct (Z.eqb_spec b bkt) as [->|Hne].
      + split; [|lia]. split; [|cbn; lia]. unfold M, ins_mem. hit4.
      + destruct (Htab b Hb) as [[Hc Hr] Hbn]. split; [|lia]. split; [|exact Hr].
        unfold M. rewrite ins_rdn_same; [exact Hc | exact Hbkt | lia | cbn; lia | cbn; unfold ins_written; intros; lia].
    - (* [comment removed for export] *)
      split; [|cbn; lia]. unfold M; unfm. peelp. hit4.
    - (* [comment removed for export] *)
      split; [|cbn; lia]. unfold M. rewrite ins_rdn_same; [exact Hmc | exact Hbkt | lia | cbn; lia | cbn; unfold ins_written; intros; lia].
    - (* [comment removed for export] *)
      unhide HBstk. unhide HBP. intros id Hid. destruct (Z.eqb_spec id (n + 1)) as [->|Hne].
      + split; [|split; [split; [|cbn; lia]|lia]].
        * unfold M; unfm. peelp. hit8.
        * unfold M; unfm. peelp. hit4.
      + destruct (Hnodes id ltac:(lia)) as (Hh & [Hl Hlr] & Hlt). split; [|split; [split; [|exact Hlr]|exact Hlt]].
        * unfold M. rewrite ins_rdn_same; [exact Hh | exact Hbkt | lia | cbn; nia | cbn; unfold ins_written; intros; nia].
        * unfold M. rewrite ins_rdn_same; [exact Hl | exact Hbkt | lia | cbn; nia | cbn; unfold ins_written; intros; nia].
    - (* [comment removed for export] *)
      split; [|cbn; lia]. unfold M; unfm. peelp. hit8.
    - (* [comment removed for export] *)
      split; [|cbn; lia]. unfold M. rewrite ins_rdn_same; [exact HPc | exact Hbkt | lia | cbn; lia | cbn; unfold ins_written; intros; lia].
    - (* [comment removed for export] *)
      split; [|cbn; lia]. unfold M; unfm. peelp. hit4.
    - cbn. lia.
  Qed.
End PUT.
