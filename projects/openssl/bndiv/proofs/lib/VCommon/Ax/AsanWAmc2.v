(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatSim StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSMat AsanSRipA AsanWMcStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma not_z : forall x : Z, (0 <= x < 2 ^ 64)%Z ->
  alu64 ALU_XOR (Z_to_bv 64 x) (sext 64 (@BV 12 4095 I)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_xor_unsigned.
  replace (bv_unsigned (sext 64 (@BV 12 4095 I))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite !bvu_z by lia.
  rewrite Z.lxor_comm. rewrite <- (Z.mod_small x (2 ^ 64)) at 1 by lia.
  rewrite <- Z.land_ones by lia. rewrite Z.land_comm.
  replace (Z.lxor (Z.ones 64) (Z.land (Z.ones 64) x)) with (Z.land (Z.ones 64) (Z.lnot x)).
  - rewrite Z.land_comm, Z.land_ones by lia. unfold Z.lnot, Z.pred.
    symmetry. apply Z.mod_unique with (-1)%Z; lia.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.testbit (Z.ones 64) i), (Z.testbit x i); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma and_m8 : forall x : Z, (0 <= x < 2 ^ 64)%Z ->
  alu64 ALU_AND (Z_to_bv 64 x) (sext 64 (@BV 12 4088 I)) = Z_to_bv 64 (8 * (x / 8)).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned.
  replace (bv_unsigned (sext 64 (@BV 12 4088 I))) with (Z.ones 64 - 7)%Z by (vm_compute; reflexivity).
  assert (Hd : (0 <= 8 * (x / 8) <= x)%Z) by (pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
  rewrite !bvu_z by lia.
  replace (Z.ones 64 - 7)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)) by (vm_compute; reflexivity).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
  rewrite (Z.testbit_ones 64 i), (Z.testbit_ones 3 i) by lia.
  replace (8 * (x / 8))%Z with (Z.shiftl (Z.shiftr x 3) 3) by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; ring).
  destruct (Z_lt_ge_dec i 3) as [L|L].
  - rewrite Z.shiftl_spec_low by lia.
    replace ((0 <=? i) && (i <? 3))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    cbn [negb]. rewrite andb_false_r, andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec by lia. rewrite Z.shiftr_spec by lia. replace (i - 3 + 3)%Z with i by ring.
    replace ((0 <=? i) && (i <? 3))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    cbn [negb]. rewrite andb_true_r.
    destruct (Z_lt_ge_dec i 64) as [L2|L2].
    + replace ((0 <=? i) && (i <? 64))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply andb_true_r.
    + replace ((0 <=? i) && (i <? 64))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      rewrite andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
      apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      pose proof (Z.pow_le_mono_r 2 64 i ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma srl3_z : forall x : Z, (0 <= x < 2 ^ 64)%Z ->
  alu64 ALU_SRL (Z_to_bv 64 x) (zext 64 (@BV 6 3 I)) = Z_to_bv 64 (x / 8).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu].
  replace (bv_and (zext 64 (@BV 6 3 I)) (Z_to_bv 64 63)) with (Z_to_bv 64 3) by (apply bv_eq; vm_compute; reflexivity).
  rewrite bv_shiftr_unsigned. rewrite !bvu_z by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition s6w (n : Z) : word := Z_to_bv 64 (n + -65).
Definition m65 : word := Z_to_bv 64 (0 + -65).

Lemma size_taken : forall n : Z, (0 <= n < 2 ^ 63)%Z ->
  branch_taken BC_GEU m65 (s6w n) = (if (n =? 0)%Z then true else (65 <=? n)%Z).
Proof.
  intros n Hn. unfold m65, s6w.
  replace (Z_to_bv 64 (0 + -65)) with (Z_to_bv 64 (2 ^ 64 - 65)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (Z_lt_ge_dec n 65) as [L|L].
  - replace (Z_to_bv 64 (n + -65)) with (Z_to_bv 64 (n + -65 + 2 ^ 64)) by (apply zw_mod).
    rewrite branch_geu_z by lia.
    destruct (n =? 0)%Z eqn:E0.
    + apply Z.eqb_eq in E0. subst n. reflexivity.
    + apply Z.eqb_neq in E0. replace (65 <=? n)%Z with false by (symmetry; apply Z.leb_gt; lia).
      apply negb_false_iff. apply Z.ltb_lt. lia.
  - rewrite branch_geu_z by lia.
    replace (n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (65 <=? n)%Z with true by (symmetry; apply Z.leb_le; lia).
    apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma load_zero8 : load_word SZ8 true (repeat (Z_to_bv 8 0) 8) = w0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma or_zero : alu64 ALU_OR w0 w0 = w0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rdn_zeros : forall segs mem (n : nat) (a : Z), (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall q, (a <= q < a + Z.of_nat n)%Z -> bat segs mem (Z_to_bv 64 q) = Some (Z_to_bv 8 0)) ->
  rdn segs mem (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  cbn [rdn repeat]. pose proof (H a ltac:(lia)) as H0. unfold bat in H0. rewrite H0.
  replace (Z_to_bv 64 a + 1) with (Z_to_bv 64 (a + 1))
    by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned; change (bv_unsigned (1 : word)) with 1%Z;
        rewrite bv_wrap_add_idemp_l; reflexivity).
  rewrite (IH (a + 1)%Z) by (try lia; intros q Hq; apply H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lbu_nz : forall v : byte, bv_unsigned v <> 0%Z ->
  branch_taken BC_EQ (load_word SZ1 false [v]) w0 = false.
Proof.
  intros v Hv. rewrite lbu_val. pose proof (byte_range v) as R. rewrite br_eq0 by lia. apply Z.eqb_neq. exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope Z_scope.

Lemma sh_range : forall x y : Z, 0 <= x -> x <= y -> y < 2 ^ 47 ->
  0x7fff8000 <= 0x7fff8000 + x / 8 /\ 0x7fff8000 + x / 8 <= 0x7fff8000 + y / 8 /\ 0x7fff8000 + y / 8 < 0x10007fff8000.
Proof. intros x y Hx Hxy Hy. lia. Qed.

(* [comment removed for export] *)
Lemma shw_range : forall x : Z, 0 <= x < 2 ^ 47 ->
  let a := 8 * ((0x7fff8000 + x / 8) / 8) in
  0x7fff8000 + x / 8 - 7 <= a /\ a <= 0x7fff8000 + x / 8 /\ 0x7fff8000 <= a /\ a + 8 <= 0x10007fff8000 /\ a mod 8 = 0.
Proof. intros x Hx a. subst a. lia. Qed.

Local Close Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mat_of_trans : forall m0 m1 m2 k1 k2, mat_of m0 m1 k1 -> mat_of m1 m2 k2 -> mat_of m0 m2 (k1 + k2).
Proof.
  intros m0 m1 m2 k1 k2 [[p1 E1] B1] [[p2 E2] B2]. split.
  - exists p2. rewrite E2. subst m1. rewrite with_lazy, with_vm_backing_twice. reflexivity.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma pg8_aligned : forall a : Z, (0 <= a < 2 ^ 64)%Z -> (a mod 8 = 0)%Z ->
  (bv_unsigned (Z_to_bv 64 a) mod 4096 + Z.of_nat 8 <= 4096)%Z.
Proof.
  intros a Ha H8. rewrite bvu_z by lia.
  pose proof (Z.mod_pos_bound a 4096 ltac:(lia)).
  assert (E : ((a mod 4096) mod 8 = 0)%Z).
  { rewrite <- (Znumtheory.Zmod_div_mod 8 4096 a) by (try lia; exists 512%Z; reflexivity). exact H8. }
  pose proof (Z.div_mod (a mod 4096) 8 ltac:(lia)). change (Z.of_nat 8) with 8%Z. lia.
Qed.

Lemma shw_pg : forall x : Z, (0 <= x < 2 ^ 47)%Z ->
  (bv_unsigned (Z_to_bv 64 (8 * ((0x7fff8000 + x / 8) / 8))) mod 4096 + Z.of_nat (msz_n SZ8) <= 4096)%Z.
Proof. intros x Hx. pose proof (shw_range x Hx) as (A1 & A2 & A3 & A4 & A5). apply pg8_aligned; lia. Qed.

Section Steps.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma xs_ld_mat : forall (m0 m : Model) (k : Z) S w sz sg rd rs1 (imm : bv 12) (x a : word) bs' (p' : word) r mm T,
  m_halted m0 = None -> mat_of m0 m k -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Load sz sg rd rs1 imm, 4%Z) ->
  rg S rs1 = x -> x + sext 64 imm = a -> ms_mem S = mm ->
  rdn segs mm a (msz_n sz) = Some bs' ->
  (bv_unsigned a mod 4096 + Z.of_nat (msz_n sz) <= 4096)%Z ->
  (vm_backing_used m0 + 4096 * (k + 1) <= vm_limit (m_vmmaps m0))%Z ->
  ms_pc_val S + Z_to_bv 64 4 = p' -> ms_resv S = r ->
  (forall m', mat_of m0 m' (k + 1) -> realizes_cfg segs cfg (mkCfg (setx S rd (load_word sz sg bs') p' r mm) m') T) ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros m0 m k S w sz sg rd rs1 imm x a bs' p' r mm T Hh Hm Hsvc HF HE HD Hx Ha Hmm Hrd Hpg Hb Hp Hr HK.
  subst x a mm p' r.
  destruct (mat_step m0 m k _ (msz_n sz) Hm ltac:(destruct sz; cbn; lia) Hpg Hb) as [m' [Em Hm']].
  eapply rzc_mat; [rewrite (mat_of_halted m0 m k Hm); exact Hh | exact Hsvc
                  | eapply wacc_Load; [exact HF | exact HE | exact HD | exact Hrd] | exact Em | ].
  exact (HK m' Hm').
Qed.

(* [comment removed for export] *)
Lemma xs_jal : forall (model : Model) S w rd (imm : bv 21) (v' p' : word) r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  ms_pc_val S + Z_to_bv 64 4 = v' -> ms_pc_val S + sext 64 imm = p' -> ms_resv S = r -> ms_mem S = m ->
  realizes_cfg segs cfg (mkCfg (setx S rd v' p' r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros model S w rd imm v' p' r m T Hh Hsvc HF HE HD <- <- <- <- Hc.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Jal; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

Lemma xs_jalr : forall (model : Model) S w rd rs1 (imm : bv 12) (x v' p' : word) r m T,
  m_halted model = None -> ms_svc_pending S = None ->
  fetch_word segs (ms_pc_val S) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  rg S rs1 = x -> ms_pc_val S + Z_to_bv 64 4 = v' -> bv_and (x + sext 64 imm) (bv_not w1) = p' ->
  ms_resv S = r -> ms_mem S = m ->
  realizes_cfg segs cfg (mkCfg (setx S rd v' p' r m) model) T ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros model S w rd rs1 imm x v' p' r m T Hh Hsvc HF HE HD <- <- <- <- <- Hc.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Jalr; [exact HF | exact HE | exact HD] | apply acc_ok_nil | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma xs_got : forall (model : Model) S base o rd g v T,
  pair_ok segs base o rd rd g = true -> is_x0 rd = false -> (0 <= g)%Z -> (g + 8 <= 2 ^ 64)%Z ->
  m_halted model = None -> ms_svc_pending S = None -> ms_pc_val S = pcw base o ->
  cell8 segs (ms_mem S) g v -> no_lazy model g (g + 8) ->
  (forall (X : word) r m, r = ms_resv S -> m = ms_mem S ->
     realizes_cfg segs cfg (mkCfg (setx (setx S rd X (pcw base (o + 4)) r m) rd (Z_to_bv 64 v) (pcw base (o + 4 + 4)) r m) model) T) ->
  realizes_cfg segs cfg (mkCfg S model) T.
Proof.
  intros model S base o rd g v T P Hx0 Hg0 Hg1 Hh Hsvc Hpc (l & Hl & Hv) Hnl HK.
  destruct (pair_ok_sound _ _ _ _ _ _ P ltac:(lia)) as (wa & wl & ia & il & HFa & HEa & HDa & HFl & HEl & HDl & HAd).
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Auipc; [rewrite Hpc; exact HFa | exact HEa | exact HDa] | apply acc_ok_nil |].
  assert (Ead : rg (setx S rd (ms_pc_val S + sext 64 (bv_concat 32 ia (Z_to_bv 12 0))) (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (ms_mem S)) rd
                + sext 64 il = Z_to_bv 64 g).
  { rewrite rg_setx_same by exact Hx0. rewrite Hpc, pcw_sext. exact HAd. }
  eapply rzc_acc; [exact Hh | reflexivity
                  | eapply (wacc_Load segs _ _ _ _ _ _ _ _ l); [rewrite pc_setx, Hpc, pcw_add; exact HFl | exact HEl | exact HDl
                                                              | rewrite Ead, mem_setx; exact Hl ]
                  | rewrite Ead; apply acc_ok_one; rewrite bvu_z by lia; [cbn; lia | exact Hnl]
                  | ].
  rewrite Hv. rewrite !pc_setx, Hpc, !pcw_add.
  exact (HK _ _ _ eq_refl eq_refl).
Qed.

End Steps.
