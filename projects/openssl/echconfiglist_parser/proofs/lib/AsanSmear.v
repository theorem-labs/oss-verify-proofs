(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefLayout AsanAcct AsanAcctShape.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanNodesAux AsanStartLoops AsanPlanCore Scfg.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ones_from (k y : Z) : Prop :=
  0 <= y < 2 ^ 47 /\ forall n, k <= n < 47 -> Z.testbit y n = true.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb.
  assert (Hn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact Hn|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (Hnz : Z.lor a b <> 0) by (intros H0; apply Z.lor_eq_0_l in H0; lia).
  assert (0 <= n) by (destruct (Z.neg_nonneg_cases n) as [Hlt|]; [|assumption]; rewrite (Z.pow_neg_r 2 n Hlt) in Ha; lia).
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftr_lt_pow2 : forall a s n, 0 <= s -> 0 <= a < 2 ^ n -> 0 <= Z.shiftr a s < 2 ^ n.
Proof.
  intros a s n Hs Ha. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma ones_from_start : forall z, 2 ^ 46 <= z < 2 ^ 47 -> ones_from 46 z.
Proof.
  intros z Hz. split; [lia|]. intros n Hn. assert (n = 46) by lia. subst n.
  apply Z.testbit_true; [lia|]. replace (z / 2 ^ 46) with 1; [reflexivity|].
  apply Z.div_unique with (r := z - 2 ^ 46); [left; lia | lia].
Qed.

Lemma ones_from_step : forall k s y, ones_from k y -> 0 <= s <= k -> k + s <= 47 ->
  ones_from (k - s) (Z.lor y (Z.shiftr y s)).
Proof.
  intros k s y [Hy Hb] Hs Hks. split.
  - apply lor_lt_pow2; [lia|]. apply shiftr_lt_pow2; lia.
  - intros n Hn. rewrite Z.lor_spec. destruct (Z_lt_le_dec n k) as [Hl|Hge].
    + rewrite (Z.shiftr_spec y s n) by lia. rewrite (Hb (n + s)) by lia. apply orb_true_r.
    + rewrite (Hb n) by lia. reflexivity.
Qed.

Lemma testbit_high_false : forall y n, 0 <= y < 2 ^ 47 -> 47 <= n -> Z.testbit y n = false.
Proof.
  intros y n Hy Hn. destruct (Z.eq_dec y 0) as [->|Ny]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 47; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Definition smear1 (z : Z) : Z := Z.lor z (Z.shiftr z 1).
Definition smear2 (z : Z) : Z := Z.lor (smear1 z) (Z.shiftr (smear1 z) 2).
Definition smear3 (z : Z) : Z := Z.lor (smear2 z) (Z.shiftr (smear2 z) 4).
Definition smear4 (z : Z) : Z := Z.lor (smear3 z) (Z.shiftr (smear3 z) 8).
Definition smear5 (z : Z) : Z := Z.lor (smear4 z) (Z.shiftr (smear4 z) 16).

Lemma smear5_ones : forall z, 2 ^ 46 <= z < 2 ^ 47 -> ones_from 15 (smear5 z).
Proof.
  intros z Hz.
  pose proof (ones_from_start z Hz) as P0.
  pose proof (ones_from_step 46 1 _ P0 ltac:(lia) ltac:(lia)) as P1.
  pose proof (ones_from_step 45 2 _ P1 ltac:(lia) ltac:(lia)) as P2.
  pose proof (ones_from_step 43 4 _ P2 ltac:(lia) ltac:(lia)) as P3.
  pose proof (ones_from_step 39 8 _ P3 ltac:(lia) ltac:(lia)) as P4.
  pose proof (ones_from_step 31 16 _ P4 ltac:(lia) ltac:(lia)) as P5.
  exact P5.
Qed.

Lemma smear_hi15 : forall z, 2 ^ 46 <= z < 2 ^ 47 -> Z.shiftr (smear5 z) 32 = 32767.
Proof.
  intros z Hz. destruct (smear5_ones z Hz) as [Hy Hb].
  change 32767 with (Z.ones 15). apply Z.bits_inj'. intros n Hn.
  rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec n 15) as [Hl|Hge].
  - rewrite (Hb (n + 32)) by lia. symmetry. apply Z.ltb_lt. lia.
  - rewrite testbit_high_false by lia. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma smear_all47 : forall z, 2 ^ 46 <= z < 2 ^ 47 -> Z.lor (smear5 z) (Z.shiftr (smear5 z) 32) = 2 ^ 47 - 1.
Proof.
  intros z Hz. destruct (smear5_ones z Hz) as [Hy Hb].
  change (2 ^ 47 - 1) with (Z.ones 47). apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z_lt_le_dec n 15) as [Hl|Hge].
  - rewrite (Hb (n + 32)) by lia. rewrite orb_true_r. symmetry. apply Z.ltb_lt. lia.
  - destruct (Z_lt_le_dec n 47) as [Hl2|Hge2].
    + rewrite (Hb n) by lia. symmetry. apply Z.ltb_lt. lia.
    + rewrite !testbit_high_false by lia. symmetry. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma smear_bounds : forall z, 2 ^ 46 <= z < 2 ^ 47 ->
  0 <= smear1 z < 2 ^ 47 /\ 0 <= smear2 z < 2 ^ 47 /\ 0 <= smear3 z < 2 ^ 47 /\ 0 <= smear4 z < 2 ^ 47 /\ 0 <= smear5 z < 2 ^ 47.
Proof.
  intros z Hz.
  pose proof (ones_from_start z Hz) as P0.
  pose proof (ones_from_step 46 1 _ P0 ltac:(lia) ltac:(lia)) as P1.
  pose proof (ones_from_step 45 2 _ P1 ltac:(lia) ltac:(lia)) as P2.
  pose proof (ones_from_step 43 4 _ P2 ltac:(lia) ltac:(lia)) as P3.
  pose proof (ones_from_step 39 8 _ P3 ltac:(lia) ltac:(lia)) as P4.
  pose proof (ones_from_step 31 16 _ P4 ltac:(lia) ltac:(lia)) as P5.
  unfold smear5, smear4, smear3, smear2, smear1. unfold ones_from in *. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Lemma D_sm0 : decode_any (0x00155593%bv : bv 32) = Some (ShiftImm ALU_SRL 11 10 1, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm1 : decode_any (0x55555637%bv : bv 32) = Some (Lui 12 349525, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm2 : decode_any (0x333336b7%bv : bv 32) = Some (Lui 13 209715, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm3 : decode_any (0x0f0f1737%bv : bv 32) = Some (Lui 14 61681, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm4 : decode_any (0x010107b7%bv : bv 32) = Some (Lui 15 4112, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm5 : decode_any (0x00b56533%bv : bv 32) = Some (Op ALU_OR 10 10 11, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm6 : decode_any (0x5556059b%bv : bv 32) = Some (OpImm32 11 12 1365, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm7 : decode_any (0x3336861b%bv : bv 32) = Some (OpImm32 12 13 819, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm8 : decode_any (0xf0f7069b%bv : bv 32) = Some (OpImm32 13 14 3855, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm9 : decode_any (0x1017871b%bv : bv 32) = Some (OpImm32 14 15 257, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm10 : decode_any (0x00255793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 2, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm11 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm12 : decode_any (0x02059793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 11 32, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm13 : decode_any (0x00f585b3%bv : bv 32) = Some (Op ALU_ADD 11 11 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm14 : decode_any (0x02061793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 12 32, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm15 : decode_any (0x00f60633%bv : bv 32) = Some (Op ALU_ADD 12 12 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm16 : decode_any (0x02069793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 13 32, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm17 : decode_any (0x00f686b3%bv : bv 32) = Some (Op ALU_ADD 13 13 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm18 : decode_any (0x02071793%bv : bv 32) = Some (ShiftImm ALU_SLL 15 14 32, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm19 : decode_any (0x00f70733%bv : bv 32) = Some (Op ALU_ADD 14 14 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm20 : decode_any (0x00455793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 4, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm21 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm22 : decode_any (0x00855793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 8, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm23 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm24 : decode_any (0x01055793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 16, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm25 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm26 : decode_any (0x02055793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 10 32, 4%Z). Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma D_sm27 : decode_any (0x00f56533%bv : bv 32) = Some (Op ALU_OR 10 10 15, 4%Z). Proof. vm_refl. Qed.

(* [comment removed for export] *)
Lemma u_v_srli : forall (a : word) s, 0 <= s -> bv_unsigned (v_srli a s) = Z.shiftr (bv_unsigned a) s.
Proof.
  intros a s Hs. unfold v_srli. pose proof (u64_range a) as Ra.
  pose proof (shiftr_lt_pow2 (bv_unsigned a) s 64 Hs ltac:(change (2 ^ 64) with 18446744073709551616; lia)) as B.
  rewrite u64_lit; [reflexivity|]. change (2 ^ 64) with 18446744073709551616 in B. lia.
Qed.

Lemma u_v_or47 : forall (a b : word), bv_unsigned a < 2 ^ 47 -> bv_unsigned b < 2 ^ 47 ->
  bv_unsigned (v_or a b) = Z.lor (bv_unsigned a) (bv_unsigned b) /\ bv_unsigned (v_or a b) < 2 ^ 47.
Proof.
  intros a b Ha Hb. unfold v_or. pose proof (u64_range a) as Ra. pose proof (u64_range b) as Rb.
  pose proof (lor_lt_pow2 (bv_unsigned a) (bv_unsigned b) 47 ltac:(lia) ltac:(lia)) as B.
  assert (2 ^ 47 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
  rewrite u64_lit by lia. lia.
Qed.

Lemma u_smear_step : forall (a : word) s, 0 <= s -> bv_unsigned a < 2 ^ 47 ->
  bv_unsigned (v_or a (v_srli a s)) = Z.lor (bv_unsigned a) (Z.shiftr (bv_unsigned a) s)
  /\ bv_unsigned (v_or a (v_srli a s)) < 2 ^ 47.
Proof.
  intros a s Hs Ha. pose proof (u64_range a) as Ra.
  pose proof (shiftr_lt_pow2 (bv_unsigned a) s 47 Hs ltac:(lia)) as B.
  rewrite <- (u_v_srli a s Hs) in B |- *. apply u_v_or47; lia.
Qed.

(* [comment removed for export] *)
Lemma smear_value : forall a0 : word, 2 ^ 46 <= bv_unsigned a0 < 2 ^ 47 ->
  let S1 := v_or a0 (v_srli a0 1) in let S2 := v_or S1 (v_srli S1 2) in let S3 := v_or S2 (v_srli S2 4) in
  let S4 := v_or S3 (v_srli S3 8) in let S5 := v_or S4 (v_srli S4 16) in
  v_or S5 (v_srli S5 32) = Z_to_bv 64 (2 ^ 47 - 1) /\ v_srli S5 32 = Z_to_bv 64 32767.
Proof.
  intros a0 Ha0. cbn zeta.
  destruct (u_smear_step a0 1 ltac:(lia) ltac:(lia)) as [U1 B1].
  destruct (u_smear_step _ 2 ltac:(lia) B1) as [U2 B2]. rewrite U1 in U2.
  destruct (u_smear_step _ 4 ltac:(lia) B2) as [U3 B3]. rewrite U2 in U3.
  destruct (u_smear_step _ 8 ltac:(lia) B3) as [U4 B4]. rewrite U3 in U4.
  destruct (u_smear_step _ 16 ltac:(lia) B4) as [U5 B5]. rewrite U4 in U5.
  change (Z.lor (bv_unsigned a0) (Z.shiftr (bv_unsigned a0) 1)) with (smear1 (bv_unsigned a0)) in *.
  change (Z.lor (smear1 (bv_unsigned a0)) (Z.shiftr (smear1 (bv_unsigned a0)) 2)) with (smear2 (bv_unsigned a0)) in *.
  change (Z.lor (smear2 (bv_unsigned a0)) (Z.shiftr (smear2 (bv_unsigned a0)) 4)) with (smear3 (bv_unsigned a0)) in *.
  change (Z.lor (smear3 (bv_unsigned a0)) (Z.shiftr (smear3 (bv_unsigned a0)) 8)) with (smear4 (bv_unsigned a0)) in *.
  change (Z.lor (smear4 (bv_unsigned a0)) (Z.shiftr (smear4 (bv_unsigned a0)) 16)) with (smear5 (bv_unsigned a0)) in *.
  destruct (u_smear_step _ 32 ltac:(lia) B5) as [U6 B6]. rewrite U5 in U6.
  rewrite (smear_all47 _ Ha0) in U6.
  split.
  - apply bv_eq. rewrite U6. rewrite u64_lit; [reflexivity|]. lia.
  - apply bv_eq. rewrite (u_v_srli _ 32) by lia. rewrite U5, (smear_hi15 _ Ha0). rewrite u64_lit; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Local Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Lemma reg_neq_of_eqb : forall a b : bv 5, bv_eqb a b = false -> a <> b.
Proof. intros a b H E. subst b. rewrite bv_eqb_refl in H. discriminate H. Qed.
(* [comment removed for export] *)
Fixpoint sm_upd_chain (Y : bvmap 5 word) (l : list (bv 5 * word)) : bvmap 5 word :=
  match l with
  | [] => Y
  | (rd, v) :: l' => regupd (sm_upd_chain Y l') rd v
  end.
Fixpoint sm_chain_look (l : list (bv 5 * word)) (r : bv 5) : option word :=
  match l with
  | [] => None
  | (rd, v) :: l' => if bv_eqb r rd then Some v else sm_chain_look l' r
  end.
Lemma sm_getr_hit : forall X Y l r v,
  X = sm_upd_chain Y l -> sm_chain_look l r = Some v -> bv_eqb r 0 = false -> getr X r = v.
Proof.
  intros X Y l r v -> H H0. induction l as [|[rd v'] l IH]; cbn [sm_upd_chain sm_chain_look] in *; [discriminate H|].
  destruct (bv_eqb r rd) eqn:E.
  - injection H as ->. assert (r = rd) as <- by (apply bv_eq; apply Z.eqb_eq; exact E).
    apply getr_same. apply reg_neq_of_eqb. exact H0.
  - rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.
Lemma sm_getr_miss : forall X Y l r,
  X = sm_upd_chain Y l -> sm_chain_look l r = None -> getr X r = getr Y r.
Proof.
  intros X Y l r -> H. induction l as [|[rd v'] l IH]; cbn [sm_upd_chain sm_chain_look] in *; [reflexivity|].
  destruct (bv_eqb r rd) eqn:E; [discriminate H|].
  rewrite getr_other by (apply reg_neq_of_eqb; exact E). apply IH. exact H.
Qed.
Local Ltac sm_chain_ulist X :=
  lazymatch X with
  | regupd ?Y ?rd ?v => let l := sm_chain_ulist Y in uconstr:(@cons (bv 5 * word) (@pair (bv 5) word rd v) l)
  | _ => uconstr:(@nil (bv 5 * word))
  end.
Local Ltac sm_chain_base X :=
  lazymatch X with
  | regupd ?Y _ _ => sm_chain_base Y
  | _ => X
  end.
Local Ltac sm_chain_val X r :=
  lazymatch X with
  | regupd ?Y ?rd ?v =>
      match tt with
      | _ => let chk := match tt with _ => constr_eq rd r end in constr:(@Some word v)
      | _ => sm_chain_val Y r
      end
  | _ => constr:(@None word)
  end.
Local Ltac getr_proof X r :=
  let l := sm_chain_ulist X in
  let Y := sm_chain_base X in
  let fv := sm_chain_val X r in
  lazymatch fv with
  | Some ?v => uconstr:(sm_getr_hit X Y l r v (@eq_refl (bvmap 5 word) X) (@eq_refl (option word) (@Some word v)) (@eq_refl bool false))
  | None => uconstr:(sm_getr_miss X Y l r (@eq_refl (bvmap 5 word) X) (@eq_refl (option word) (@None word)))
  end.
Local Ltac gres :=
  repeat match goal with
         | |- context [getr ?X ?r] =>
             lazymatch X with regupd _ _ _ => idtac end;
             let p := getr_proof X r in
             let p' := constr:(p) in rewrite p'
         end.

Section SmearCode.
  Variable SEGS : list Segment.
  Variable x : Z.
  Hypothesis Hx : 0 <= x /\ x + 112 < 2 ^ 64.
  Hypothesis FW :
       fetch_word SEGS (Z_to_bv 64 x) = Some (0x00155593%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some (0x55555637%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some (0x333336b7%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 12)) = Some (0x0f0f1737%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 16)) = Some (0x010107b7%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 20)) = Some (0x00b56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 24)) = Some (0x5556059b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 28)) = Some (0x3336861b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 32)) = Some (0xf0f7069b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 36)) = Some (0x1017871b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 40)) = Some (0x00255793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 44)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 48)) = Some (0x02059793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 52)) = Some (0x00f585b3%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 56)) = Some (0x02061793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 60)) = Some (0x00f60633%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 64)) = Some (0x02069793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 68)) = Some (0x00f686b3%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 72)) = Some (0x02071793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 76)) = Some (0x00f70733%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 80)) = Some (0x00455793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 84)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 88)) = Some (0x00855793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 92)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 96)) = Some (0x01055793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 100)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 104)) = Some (0x02055793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x + 108)) = Some (0x00f56533%bv : bv 32).
  

  (* [comment removed for export] *)
  Local Ltac sm_step F D nextpc :=
    eapply mst_step;
    [ reflexivity
    | lazymatch type of D with
      | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) => exact (step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
      | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) => exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
      | decode_any _ = Some (Op ALU_OR _ _ _, _) => exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
      | decode_any _ = Some (Op ALU_ADD _ _ _, _) => exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
      | decode_any _ = Some (OpImm32 _ _ _, _) => exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
      | decode_any _ = Some (Lui _ _, _) => exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
      end
    | ];
    rif; rewrite v_addi_lit by lia; pc_is nextpc; gres; imm_norm.

  Lemma smear_steps : forall regs M rom,
    2 ^ 46 <= bv_unsigned (getr regs 10) < 2 ^ 47 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 112)) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
      /\ getr regs' 11 = Z_to_bv 64 0x5555555555555555
      /\ getr regs' 12 = Z_to_bv 64 0x3333333333333333
      /\ getr regs' 13 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f
      /\ getr regs' 14 = Z_to_bv 64 0x0101010101010101
      /\ getr regs' 15 = Z_to_bv 64 32767
      /\ (forall r : bv 5, r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r)%bv.
  Proof.
    intros regs M rom Ha0.
    destruct FW as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19
                    & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    eexists. split.
    { sm_step F0 D_sm0 (x + 4).
      sm_step F1 D_sm1 (x + 8).
      sm_step F2 D_sm2 (x + 12).
      sm_step F3 D_sm3 (x + 16).
      sm_step F4 D_sm4 (x + 20).
      sm_step F5 D_sm5 (x + 24).
      sm_step F6 D_sm6 (x + 28).
      sm_step F7 D_sm7 (x + 32).
      sm_step F8 D_sm8 (x + 36).
      sm_step F9 D_sm9 (x + 40).
      sm_step F10 D_sm10 (x + 44).
      sm_step F11 D_sm11 (x + 48).
      sm_step F12 D_sm12 (x + 52).
      sm_step F13 D_sm13 (x + 56).
      sm_step F14 D_sm14 (x + 60).
      sm_step F15 D_sm15 (x + 64).
      sm_step F16 D_sm16 (x + 68).
      sm_step F17 D_sm17 (x + 72).
      sm_step F18 D_sm18 (x + 76).
      sm_step F19 D_sm19 (x + 80).
      sm_step F20 D_sm20 (x + 84).
      sm_step F21 D_sm21 (x + 88).
      sm_step F22 D_sm22 (x + 92).
      sm_step F23 D_sm23 (x + 96).
      sm_step F24 D_sm24 (x + 100).
      sm_step F25 D_sm25 (x + 104).
      sm_step F26 D_sm26 (x + 108).
      sm_step F27 D_sm27 (x + 112).
      apply mst_refl. }
    pose proof (smear_value (getr regs 10) Ha0) as [V10 V15].
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - gres. exact V10.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. exact V15.
    - intros r N10 N11 N12 N13 N14 N15. repeat (rewrite getr_other; [|assumption]). reflexivity.
  Qed.
End SmearCode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SmearNode.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Context {SC : StepCfg}.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Hypothesis Xsm : 0 <= x_smear A /\ x_smear A + 112 < 2 ^ 64.
  Hypothesis FWA :
       fetch_word SEGS (Z_to_bv 64 (x_smear A)) = Some (0x00155593%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 4)) = Some (0x55555637%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 8)) = Some (0x333336b7%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 12)) = Some (0x0f0f1737%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 16)) = Some (0x010107b7%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 20)) = Some (0x00b56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 24)) = Some (0x5556059b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 28)) = Some (0x3336861b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 32)) = Some (0xf0f7069b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 36)) = Some (0x1017871b%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 40)) = Some (0x00255793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 44)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 48)) = Some (0x02059793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 52)) = Some (0x00f585b3%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 56)) = Some (0x02061793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 60)) = Some (0x00f60633%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 64)) = Some (0x02069793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 68)) = Some (0x00f686b3%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 72)) = Some (0x02071793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 76)) = Some (0x00f70733%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 80)) = Some (0x00455793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 84)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 88)) = Some (0x00855793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 92)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 96)) = Some (0x01055793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 100)) = Some (0x00f56533%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 104)) = Some (0x02055793%bv : bv 32)
    /\ fetch_word SEGS (Z_to_bv 64 (x_smear A + 108)) = Some (0x00f56533%bv : bv 32).
  


  #[local] Notation Hv := (AsanNodesAux.Hv A).
  #[local] Notation lazy_cover_vis := (AsanNodesAux.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (AsanNodesAux.H_off_segments_vis SEGS A SEGS_in_hull).

  Theorem x_sound_smear : x_stmt SEGS A nx0 LIMIT SINV argH FS0 XSmear.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_smear in Hn.
    destruct (negb (Z.eqb (pc cs) (x_smear A))) eqn:Hpc; [discriminate|]. apply negb_false_iff in Hpc. apply Z.eqb_eq in Hpc.
    destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
    destruct (Z.leb (2 ^ 46) lo && Z.ltb hi (2 ^ 47))%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as L1.
    pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as L2.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    assert (Ha0 : 2 ^ 46 <= bv_unsigned (getr R 10) < 2 ^ 47) by (rewrite H10; lia).
    set (H2 := Hv E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    destruct (smear_steps SEGS (x_smear A) Xsm FWA R (mrestrict H2 FULL) (seg_rom SEGS) Ha0)
      as [R' (Hms & P10 & P11 & P12 & P13 & P14 & P15 & Pag)].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_smear A + 112)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_smear A + 112)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_smear A + 112)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with
    | |- cs_ok ?sg ?aa ?lim ?sinv ?ah ?fs ?EE _ ?RR ?FF ?mm =>
        change (cs_ok sg aa lim sinv ah fs EE
                  (with_ss cs
                     (mk_ss (x_smear A + 0x70)
                        (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (s_regs (a_ss cs))
                           10 (ELit (2 ^ 47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
                           13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff))
                        (s_know (a_ss cs)) (s_next (a_ss cs))))
                  RR FF mm)
    end.
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
    cbn [s_regs s_know s_next s_pc mk_ss].
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    pose proof (regs_ok_set_n E _ _ 10 (ELit (2 ^ 47 - 1)) _ HR ltac:(lia) (edenot_lit E _)) as K10.
    pose proof (regs_ok_set_n E _ _ 11 (ELit 0x5555555555555555) _ K10 ltac:(lia) (edenot_lit E _)) as K11.
    pose proof (regs_ok_set_n E _ _ 12 (ELit 0x3333333333333333) _ K11 ltac:(lia) (edenot_lit E _)) as K12.
    pose proof (regs_ok_set_n E _ _ 13 (ELit 0x0f0f0f0f0f0f0f0f) _ K12 ltac:(lia) (edenot_lit E _)) as K13.
    pose proof (regs_ok_set_n E _ _ 14 (ELit 0x0101010101010101) _ K13 ltac:(lia) (edenot_lit E _)) as K14.
    pose proof (regs_ok_set_n E _ _ 15 (ELit 32767) _ K14 ltac:(lia) (edenot_lit E _)) as K15.
    clear K10 K11 K12 K13 K14.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 13)) with (13%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 15)) with (15%bv : bv 5) in K15 by (apply bv_eq; reflexivity).
    intros r. rewrite <- (K15 r).
    destruct (decide (r = 15%bv)) as [->|N15]; [rewrite getr_same by reg_neq_tac; exact P15 | rewrite (getr_other _ _ _ _ N15)].
    destruct (decide (r = 14%bv)) as [->|N14]; [rewrite getr_same by reg_neq_tac; exact P14 | rewrite (getr_other _ _ _ _ N14)].
    destruct (decide (r = 13%bv)) as [->|N13]; [rewrite getr_same by reg_neq_tac; exact P13 | rewrite (getr_other _ _ _ _ N13)].
    destruct (decide (r = 12%bv)) as [->|N12]; [rewrite getr_same by reg_neq_tac; exact P12 | rewrite (getr_other _ _ _ _ N12)].
    destruct (decide (r = 11%bv)) as [->|N11]; [rewrite getr_same by reg_neq_tac; exact P11 | rewrite (getr_other _ _ _ _ N11)].
    destruct (decide (r = 10%bv)) as [->|N10]; [rewrite getr_same by reg_neq_tac; exact P10 | rewrite (getr_other _ _ _ _ N10)].
    exact (Pag r N10 N11 N12 N13 N14 N15).
  Qed.
End SmearNode.
