(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefReadLib HB_code_rp.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require RtMemIsZero HBSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zbv_u : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

Lemma zbv_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma v_addi_zbv : forall z i, (0 <= z < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof. intros z i Hz. unfold v_addi. rewrite zbv_u by exact Hz. reflexivity. Qed.

Lemma v_add_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb. unfold v_add. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_sub_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b Ha Hb. unfold v_sub. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_or_zero : forall (x : word), v_or x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_r. apply zbv_self.
Qed.

Lemma v_or_zero_l : forall (x : word), v_or (Z_to_bv 64 0) x = x.
Proof.
  intros x. unfold v_or. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.lor_0_l. apply zbv_self.
Qed.

Lemma land_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> Z.land z (2 ^ 64 - 8) = (z / 8 * 8)%Z.
Proof.
  intros z Hz.
  assert (E : (2 ^ 64 - 8)%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  rewrite E. transitivity (Z.ldiff (Z.land z (Z.ones 64)) (Z.ones 3)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit z i), (Z.testbit (Z.ones 64) i), (Z.testbit (Z.ones 3) i); reflexivity. }
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_andi_m8 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) (-8) = Z_to_bv 64 (z / 8 * 8).
Proof.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z. rewrite land_m8 by exact Hz. reflexivity.
Qed.

Lemma c_ltu_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma c_eq_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b)%Z.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma v_sltiu_zero1 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof. reflexivity. Qed.

Lemma zbv_add1 : forall a, Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  apply Zplus_mod_idemp_l.
Qed.

(* [comment removed for export] *)
Lemma wbytes_none_back : forall bs m a x, wbytes m a bs x = None -> m x = None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn [wbytes] in H; [exact H|].
  apply IH in H. destruct (bv_eqb x a); [discriminate | exact H].
Qed.
Lemma store_ok1_wbytes : forall m a bs x,
  store_ok SEGS m x 1 = true -> store_ok SEGS (wbytes m a bs) x 1 = true.
Proof.
  intros m a bs x H. cbn [store_ok] in H |- *. unfold wview in H |- *.
  destruct (wbytes m a bs x) eqn:E; [reflexivity|].
  rewrite (wbytes_none_back _ _ _ _ E) in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma store_ok_bytes : forall nb m (a : Z),
  (0 <= a)%Z -> (a + Z.of_nat nb < 2 ^ 64)%Z ->
  (forall j, (0 <= j < Z.of_nat nb)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) nb = true.
Proof.
  induction nb as [|nb IH]; intros m a Ha Hw H; [reflexivity|].
  cbn [store_ok]. pose proof (H 0%Z ltac:(lia)) as H0. cbn [store_ok] in H0. rewrite Z.add_0_r in H0.
  destruct (wview SEGS m (Z_to_bv 64 a)); [|discriminate].
  rewrite zbv_add1. apply IH; [lia|lia|].
  intros j Hj. replace (a + 1 + j)%Z with (a + (1 + j))%Z by lia. apply H. lia.
Qed.
Lemma store_ok8_bytes : forall m (a : Z),
  (0 <= a)%Z -> (a + 8 < 2 ^ 64)%Z ->
  (forall j, (0 <= j < 8)%Z -> store_ok SEGS m (Z_to_bv 64 (a + j)) 1 = true) ->
  store_ok SEGS m (Z_to_bv 64 a) 8 = true.
Proof. intros m a Ha Hw H. apply store_ok_bytes; [exact Ha | cbn; lia | exact H]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record mzH (mem : word -> option byte) (ub n usp : Z) : Prop := {
  mz_n    : (0 <= n <= 2 ^ 40)%Z;
  mz_ub   : (0 <= ub)%Z;
  mz_nw   : (ub + n + 8 < 2 ^ 64)%Z;
  mz_sp   : (16 <= usp < 2 ^ 64)%Z;
  mz_disj : (ub + n <= usp - 8 \/ usp <= ub)%Z;
  mz_zero : forall i, (0 <= i < n)%Z -> mem (Z_to_bv 64 (ub + i)) = Some (Z_to_bv 8 0);
  mz_stk  : store_ok SEGS mem (Z_to_bv 64 (usp - 8)) 8 = true
}.
Definition mz_clob (r : reg) : bool :=
  (bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16)%bool.

Lemma rdn1 : forall m (a : word) b, m a = Some b -> rdn SEGS m a 1 = Some [b].
Proof. intros m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Theorem as_mem_is_zero : forall (mem rom : word -> option byte) (ub n usp : Z) (ra : word),
  mzH mem ub n usp ->
  forall regs,
    ret_ok ra ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
    getr regs 10 = Z_to_bv 64 ub -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs HBSums.ha_mem_is_zero_entry mem rom)
                  (mkst regs' ra (wbytes mem (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 ra)) rom)
      /\ getr regs' 10 = Z_to_bv 64 1
      /\ getr regs' 2 = Z_to_bv 64 usp
      /\ getr regs' 1 = ra
      /\ (forall r, mz_clob r = false -> r <> 2 -> r <> 1 -> getr regs' r = getr regs r).
Proof.
  intros mem rom ub n usp ra H regs Hret H1 H2 H10 H11.
  destruct H as [Hn Hub Hnw Hsp Hdisj Hz Hstk].
  assert (U1 : bv_unsigned (Z_to_bv 64 ub) = ub) by (apply zbv_u; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply zbv_u; lia).
  destruct (HBSums.ha_mem_is_zero mem (Z_to_bv 64 ub) (Z_to_bv 64 usp) n rom regs ra) as (regs' & Hms & Hag & Ha0 & Hsp' & Hra');
    rewrite ?U1, ?U2; try assumption; try lia.
  - intros a Ha. apply rdn1. replace a with (Z_to_bv 64 (ub + (bv_unsigned a - ub))) by (rewrite <- (zbv_self a) at 2; f_equal; lia).
    apply Hz. lia.
  - rewrite U2 in Hms. exists regs'. split; [exact Hms|]. split; [exact Ha0|]. split; [exact Hsp'|]. split; [exact Hra'|].
    intros r Hr N2 N1. apply Hag. unfold RtMemIsZero.memisz_clob. cbn [In].
    unfold mz_clob in Hr. repeat (apply orb_false_iff in Hr; destruct Hr as [Hr ?]).
    intros [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; subst r;
      match goal with H : bv_eqb ?x ?x = false |- _ => rewrite bv_eqb_refl in H; discriminate H | _ => idtac end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SB : Z := 0x7fff8000.           (* [comment removed for export] *)
Definition kLowEnd : Z := 0x7fff7fff.      (* [comment removed for export] *)
Definition kHighBeg : Z := 0x10007fff8000. (* [comment removed for export] *)
Definition kHighEnd : Z := 0x7fffffffffff. (* [comment removed for export] *)

Lemma SB_val : SB = 0x7fff8000%Z. Proof. reflexivity. Qed.

Lemma v_srli_3 : forall z, (0 <= z < 2 ^ 64)%Z -> v_srli (Z_to_bv 64 z) 3 = Z_to_bv 64 (z / 8).
Proof. intros z Hz. unfold v_srli. rewrite zbv_u by exact Hz. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_andi_7 : forall z, (0 <= z < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 z) 7 = Z_to_bv 64 (z mod 8).
Proof.
  intros z Hz. unfold v_andi. rewrite zbv_u by exact Hz. change (bv_wrap 64 7) with (Z.ones 3).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma k_low_val :
  v_and (v_addi (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB + -1))) (-1)) (Z_to_bv 64 (SB + -1)) = Z_to_bv 64 kLowEnd.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma k_m1_val : v_addi (Z_to_bv 64 0) (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma k_hse_val : v_add (v_srli (Z_to_bv 64 kHighEnd) 3) (Z_to_bv 64 SB) = Z_to_bv 64 (kHighBeg - 1).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma lit_83d10 : v_addi (0x1c05a0 : word) 4 = (0x1c05a4 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lit_83d1c : v_addi (0x1c05ac : word) 4 = (0x1c05b0 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma lit_83d9c : v_addi (0x1c062c : word) 4 = (0x1c0630 : word).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma ret_ok_83d10 : ret_ok (0x1c05a4 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_83d1c : ret_ok (0x1c05b0 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_83d9c : ret_ok (0x1c0630 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_zbv : forall z, (0 <= z < 2 ^ 64)%Z -> (z mod 2 = 0)%Z -> ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply ret_ok_even. rewrite zbv_u by exact Hz. exact He. Qed.

Lemma bv_signed_small8 : forall (b : byte), (bv_unsigned b < 128)%Z -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128%Z. lia.
Qed.

Lemma c_lts_zbv : forall a b, (0 <= a < 2 ^ 63)%Z -> (0 <= b < 2 ^ 63)%Z ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b)%Z.
Proof.
  intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63)%Z; lia). reflexivity.
Qed.

Lemma bv_eq_dec : forall n (a b : bv n), {a = b} + {a <> b}.
Proof.
  intros n0 a b. destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
  - left. apply bv_eq. exact E.
  - right. intros ->. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
Definition cell (m : word -> option byte) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).

Definition cells (m : word -> option byte) : Prop :=
  cell m 0x5dead8 0x6a1a78 /\ cell m 0x6a1a78 SB
  /\ cell m 0x5deae0 0x6a2768 /\ cell m 0x6a2768 0
  /\ cell m 0x5deae8 0x6a2770 /\ cell m 0x6a2770 0
  /\ cell m 0x5deaf0 0x6a2760 /\ cell m 0x6a2760 kHighEnd.

Definition in_mem (p : Z) : Prop := (p <= kLowEnd)%Z \/ (kHighBeg <= p <= kHighEnd)%Z.

Ltac mstep L := eapply mst_step; [reflexivity | L | ]; step_simpl; imm_norm.
Ltac gr := repeat (first [ rewrite getr_same by (intros E; discriminate E)
                          | rewrite getr_other by (intros E; discriminate E) ]);
           rewrite ?Z.add_0_r, ?Z.add_0_l.
Ltac zn := rewrite ?v_addi_zbv by lia.
Ltac br_lt := gr; rewrite c_ltu_zbv by lia; first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Ltac br_eq := gr; rewrite c_eq_zbv by lia; first [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Ltac ne := intros E; discriminate E.
(* [comment removed for export] *)
Ltac mld F D v Hcell Hbase :=
  mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 v) F eq_refl D);
               [ gr; rewrite ?Hbase; imm_norm; zn;
                 match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                   first [ exact Hcell
                         | replace a with (ltac:(match type of Hcell with cell _ ?c _ => exact c end)) by lia; exact Hcell ] end
               | apply bytes_le_to_Z_8 ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition m2s_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

Lemma mem_to_shadow : forall rom regs m (p : Z) (ra : word),
  cells m -> (0 <= p)%Z -> in_mem p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ra -> ret_ok ra ->
  exists regs',
    msteps SEGS (mkst regs (0x1c0030 : word) m rom) (mkst regs' ra m rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + p / 8)
    /\ (forall r, m2s_clob r = false -> getr regs' r = getr regs r).
Proof.
  intros rom regs m p ra (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Hp Hin H10 H1 Hret.
  unfold in_mem, kLowEnd, kHighBeg, kHighEnd in Hin.
  assert (Hp64 : (p < 2 ^ 64)%Z) by lia. pose proof SB_val as HSB.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmb.
  destruct (Z.le_gt_cases p 0x7fff7fff) as [Hlow | Hhigh].
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5df030) F_1c5060 eq_refl D_1c5060);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_1c5064 D_1c5064 0x6a1a78%Z C1 H10.
      mld F_1c5068 D_1c5068 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c506c eq_refl D_1c506c)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_1c5070 eq_refl D_1c5070)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5074 eq_refl D_1c5074)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_1c5078 eq_refl D_1c5078)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c507c eq_refl D_1c507c); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c50c0 eq_refl D_1c50c0)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c50c4 eq_refl D_1c50c4)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_1c50c8 eq_refl D_1c50c8); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  - eexists. split; [|split].
    + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5df030) F_1c5060 eq_refl D_1c5060);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_1c5064 D_1c5064 0x6a1a78%Z C1 H10.
      mld F_1c5068 D_1c5068 SB C2 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c506c eq_refl D_1c506c)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_1c5070 eq_refl D_1c5070)). gr.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5074 eq_refl D_1c5074)). gr.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_1c5078 eq_refl D_1c5078)). gr.
      rewrite k_low_val. unfold kLowEnd.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c507c eq_refl D_1c507c); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5df050) F_1c5080 eq_refl D_1c5080);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_1c5084 D_1c5084 0x6a2768%Z C3 H10.
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5df058) F_1c5088 eq_refl D_1c5088);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_1c508c D_1c508c 0x6a2770%Z C5 H10.
      mld F_1c5090 D_1c5090 0%Z C4 H10.
      mld F_1c5094 D_1c5094 0%Z C6 H10.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5098 eq_refl D_1c5098)). gr. rewrite k_m1_val.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c509c eq_refl D_1c509c); gr; rewrite ?H10; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5df074) F_1c50a4 eq_refl D_1c50a4);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_1c50a8 D_1c50a8 0x6a2760%Z C7 H10.
      mld F_1c50ac D_1c50ac kHighEnd C8 H10.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c50b0 eq_refl D_1c50b0)). gr.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c50b4 eq_refl D_1c50b4)). gr. rewrite k_hse_val. unfold kHighBeg.
      replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_1c50b8 eq_refl D_1c50b8); gr; rewrite ?H10; unfold kHighEnd; br_lt).
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c50bc eq_refl D_1c50bc); gr; rewrite ?H10; br_lt).
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c50c0 eq_refl D_1c50c0)). gr. rewrite H10, (v_srli_3 p) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c50c4 eq_refl D_1c50c4)). gr. rewrite v_add_zbv by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_1c50c8 eq_refl D_1c50c8); gr; exact H1 |].
      imm_norm. rewrite Hret. apply mst_refl.
    + gr. apply (f_equal (Z_to_bv 64)). lia.
    + intros r Hr. unfold m2s_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rpH (mem : word -> option byte) (beg n usp : Z) (b1 : byte) : Prop := {
  rp_n    : (16 <= n <= 2 ^ 40)%Z;
  rp_beg  : (0 <= beg)%Z;
  rp_rng  : (beg + n <= kLowEnd)%Z \/ (kHighBeg <= beg /\ beg + n <= kHighEnd)%Z;
  rp_sp   : (80 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  rp_disj : (SB + (beg + n - 1) / 8 < usp - 72)%Z;
  (* [comment removed for export] *)
  rp_zero : forall g, (beg / 8 <= g < (beg + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  rp_last : mem (Z_to_bv 64 (SB + (beg + n - 1) / 8)) = Some b1;
  rp_b1   : bv_unsigned b1 = 0%Z \/ ((beg + n - 1) mod 8 < bv_unsigned b1 < 8)%Z;
  (* [comment removed for export] *)
  rp_stk  : forall a, (usp - 72 <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  rp_cells : cells mem
}.

Definition rp_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

(* [comment removed for export] *)
Definition rp_tmp (r : reg) : bool :=
  (rp_clob r || bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19
   || bv_eqb r 20 || bv_eqb r 21)%bool.

(* [comment removed for export] *)
Definition rp_frame (mem : word -> option byte) (usp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
  w 72%Z (Z_to_bv 64 0x1c0630) (w 56%Z s5 (w 48%Z s4 (w 40%Z s3 (w 32%Z s2 (w 24%Z s1 (w 16%Z s0 (w 8%Z ra mem))))))).

Section RP.
  Variables (mem rom : word -> option byte) (beg n usp : Z) (b1 : byte).
  Hypothesis H : rpH mem beg n usp b1.
  Variable regs0 : bvmap 5 word.   (* [comment removed for export] *)
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 beg.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 n.

  Let en : Z := (beg + n)%Z.
  Let g0 : Z := (beg / 8)%Z.
  Let g1 : Z := ((en - 1) / 8)%Z.
  Let gu : Z := ((beg + 7) / 8)%Z.
  Let ge : Z := (en / 8)%Z.

  Let Hn := rp_n _ _ _ _ _ H.
  Let Hbeg := rp_beg _ _ _ _ _ H.
  Let Hsp := rp_sp _ _ _ _ _ H.

  Lemma rng : (en <= kHighEnd)%Z /\ ((en <= kLowEnd)%Z \/ (kHighBeg <= beg)%Z).
  Proof. pose proof (rp_rng _ _ _ _ _ H) as R. unfold en, kLowEnd, kHighBeg, kHighEnd in *. lia. Qed.

  Lemma divfacts :
    (8 * g0 <= beg < 8 * g0 + 8)%Z /\ (8 * g1 <= en - 1 < 8 * g1 + 8)%Z
    /\ (8 * gu <= beg + 7 < 8 * gu + 8)%Z /\ (8 * ge <= en < 8 * ge + 8)%Z
    /\ ((en - 1) mod 8 = en - 1 - 8 * g1)%Z.
  Proof.
    unfold g0, g1, gu, ge, en.
    pose proof (Z.div_mod beg 8 ltac:(lia)). pose proof (Z.mod_pos_bound beg 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod (beg + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (beg + n) 8 ltac:(lia)).
    lia.
  Qed.

  Definition m7 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem)))))).
  Definition m8 : word -> option byte :=
    wbytes m7 (Z_to_bv 64 (usp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x1c0630)).

  Lemma m8_frame : m8 = rp_frame mem usp ra (getr regs0 8) (getr regs0 9) (getr regs0 18)
                                 (getr regs0 19) (getr regs0 20) (getr regs0 21).
  Proof. reflexivity. Qed.

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  Lemma m7_below : forall x : word, (bv_unsigned x < usp - 72)%Z -> m7 x = mem x.
  Proof.
    intros x Hx. unfold m7. rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.
  Lemma m8_below : forall x : word, (bv_unsigned x < usp - 72)%Z -> m8 x = mem x.
  Proof.
    intros x Hx. unfold m8. rewrite wbytes_below; [apply m7_below; exact Hx| |]; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  Lemma rdn_m7_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 72)%Z ->
    rdn SEGS m7 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros a k Ha Hk. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply m7_below. lia.
  Qed.
  Lemma rdn_m8_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 72)%Z ->
    rdn SEGS m8 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros a k Ha Hk. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply m8_below. lia.
  Qed.

  Lemma SB_lt : (0x6a2780 <= usp - 72)%Z.   (* [comment removed for export] *)
  Proof. pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val. lia. Qed.

  Lemma cells_m7 : cells m7.
  Proof.
    pose proof (rp_cells _ _ _ _ _ H) as C. pose proof SB_lt. unfold cells, cell in *.
    rewrite !rdn_m7_below by (cbn; lia). exact C.
  Qed.
  Lemma cells_m8 : cells m8.
  Proof.
    pose proof (rp_cells _ _ _ _ _ H) as C. pose proof SB_lt. unfold cells, cell in *.
    rewrite !rdn_m8_below by (cbn; lia). exact C.
  Qed.

  Lemma stk8 : forall m a, (usp - 72 <= a)%Z -> (a + 8 <= usp)%Z ->
    (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true) ->
    store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a H1 H2 Hm. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply Hm. apply (rp_stk _ _ _ _ _ H). lia.
  Qed.

  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := unfold m8, m7;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).

  Lemma rd_ra : rdn SEGS m8 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).            Proof. rd_slot. Qed.
  Lemma rd_s0 : rdn SEGS m8 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. rd_slot. Qed.
  Lemma rd_s1 : rdn SEGS m8 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. rd_slot. Qed.
  Lemma rd_s2 : rdn SEGS m8 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  Lemma rd_s3 : rdn SEGS m8 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  Lemma rd_s4 : rdn SEGS m8 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  Lemma rd_s5 : rdn SEGS m8 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.

  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r, rp_tmp r = false -> getr regs r = getr regs0 r.

  Ltac solve_keep Hk :=
    intros r Hr; unfold rp_tmp, rp_clob in Hr;
    repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate));
    apply Hk; unfold rp_tmp, rp_clob; exact Hr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac msd F D o v Hbase Hm :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (usp - o)) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption]
                 | apply stk8; [lia | lia | intros x Hx; repeat apply store_ok1_wbytes; exact Hx] ]).

  Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x1c04bc : word) mem rom) (mkst regs (0x1c04e8 : word) m7 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 64) /\ getr regs 8 = Z_to_bv 64 beg /\ getr regs 9 = Z_to_bv 64 n
      /\ getr regs 1 = ra /\ keep regs.
  Proof.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c54ec eq_refl D_1c54ec)). rewrite H02. zn.
      msd F_1c54f0 D_1c54f0 8%Z ra H02 mem.
      msd F_1c54f4 D_1c54f4 16%Z (getr regs0 8) H02 mem.
      msd F_1c54f8 D_1c54f8 24%Z (getr regs0 9) H02 mem.
      msd F_1c54fc D_1c54fc 32%Z (getr regs0 18) H02 mem.
      msd F_1c5500 D_1c5500 40%Z (getr regs0 19) H02 mem.
      msd F_1c5504 D_1c5504 48%Z (getr regs0 20) H02 mem.
      msd F_1c5508 D_1c5508 56%Z (getr regs0 21) H02 mem.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_1c550c eq_refl D_1c550c); gr; rewrite ?H011, ?getr_zero; br_eq).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5510 eq_refl D_1c5510)). gr. rewrite H011. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5514 eq_refl D_1c5514)). gr. rewrite H010. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      intros r Hr. unfold rp_tmp, rp_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blk_A : forall regs,
    getr regs 8 = Z_to_bv 64 beg ->
    exists regs',
      msteps SEGS (mkst regs (0x1c04e8 : word) m7 rom) (mkst regs' (0x1c0548 : word) m7 rom)
      /\ getr regs' 21 = Z_to_bv 64 0x6a1a78 /\ getr regs' 11 = Z_to_bv 64 SB /\ getr regs' 12 = Z_to_bv 64 kLowEnd
      /\ (forall r, m2s_clob r = false -> r <> 21 -> getr regs' r = getr regs r).
  Proof.
    intros regs H8.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct (Z.le_gt_cases beg 0x7fff7fff) as [Hlow | Hhigh].
    - eexists. split.
      + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de4e8) F_1c5518 eq_refl D_1c5518);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c551c D_1c551c 0x6a1a78%Z C1 H8.
        mld F_1c5520 D_1c5520 SB C2 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5524 eq_refl D_1c5524)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_1c5528 eq_refl D_1c5528)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c552c eq_refl D_1c552c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_1c5530 eq_refl D_1c5530)). gr. rewrite k_low_val. unfold kLowEnd.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c5534 eq_refl D_1c5534); gr; rewrite ?H8; br_lt).
        apply mst_refl.
      + gr. repeat split; try reflexivity.
        intros r Hr Hr21. unfold m2s_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; first [discriminate | congruence])). reflexivity.
    - eexists. split.
      + mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de4e8) F_1c5518 eq_refl D_1c5518);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c551c D_1c551c 0x6a1a78%Z C1 H8.
        mld F_1c5520 D_1c5520 SB C2 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5524 eq_refl D_1c5524)). gr. zn.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_1c5528 eq_refl D_1c5528)). gr.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c552c eq_refl D_1c552c)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_1c5530 eq_refl D_1c5530)). gr. rewrite k_low_val. unfold kLowEnd.
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c5534 eq_refl D_1c5534); gr; rewrite ?H8; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de508) F_1c5538 eq_refl D_1c5538);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c553c D_1c553c 0x6a2768%Z C3 H8.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de510) F_1c5540 eq_refl D_1c5540);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c5544 D_1c5544 0x6a2770%Z C5 H8.
        mld F_1c5548 D_1c5548 0%Z C4 H8.
        mld F_1c554c D_1c554c 0%Z C6 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5550 eq_refl D_1c5550)). gr. rewrite k_m1_val.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c5554 eq_refl D_1c5554); gr; rewrite ?H8; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de52c) F_1c555c eq_refl D_1c555c);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c5560 D_1c5560 0x6a2760%Z C7 H8.
        mld F_1c5564 D_1c5564 kHighEnd C8 H8.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c5568 eq_refl D_1c5568)). gr.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c556c eq_refl D_1c556c)). gr. rewrite k_hse_val. unfold kHighBeg.
        replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_1c5570 eq_refl D_1c5570); gr; rewrite ?H8; unfold kHighEnd; br_lt).
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c5574 eq_refl D_1c5574); gr; rewrite ?H8; br_lt).
        apply mst_refl.
      + gr. repeat split; try reflexivity.
        intros r Hr Hr21. unfold m2s_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; first [discriminate | congruence])). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition b_clob (r : reg) : bool :=
    (bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 18)%bool.

  Lemma blk_B : forall regs,
    getr regs 8 = Z_to_bv 64 beg -> getr regs 9 = Z_to_bv 64 n ->
    getr regs 11 = Z_to_bv 64 SB -> getr regs 12 = Z_to_bv 64 kLowEnd ->
    exists regs',
      msteps SEGS (mkst regs (0x1c0548 : word) m7 rom) (mkst regs' (0x1c0590 : word) m7 rom)
      /\ getr regs' 18 = Z_to_bv 64 en
      /\ (forall r, b_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H8 H9 H11 H12.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    destruct HR as [HR1 [Hlow | Hhigh]].
    - eexists. split.
      + mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c5578 eq_refl D_1c5578)). gr. rewrite H9, H8, v_add_zbv by lia.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c557c eq_refl D_1c557c); gr; rewrite ?H12; unfold kLowEnd; br_lt).
        apply mst_refl.
      + gr. split; [apply (f_equal (Z_to_bv 64)); lia|].
        intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - eexists. split.
      + mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c5578 eq_refl D_1c5578)). gr. rewrite H9, H8, v_add_zbv by lia.
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c557c eq_refl D_1c557c); gr; rewrite ?H12; unfold kLowEnd; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de550) F_1c5580 eq_refl D_1c5580);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c5584 D_1c5584 0x6a2768%Z C3 H8.
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de558) F_1c5588 eq_refl D_1c5588);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c558c D_1c558c 0x6a2770%Z C5 H8.
        mld F_1c5590 D_1c5590 0%Z C4 H8.
        mld F_1c5594 D_1c5594 0%Z C6 H8.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5598 eq_refl D_1c5598)). gr. rewrite k_m1_val.
        mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_1c559c eq_refl D_1c559c); gr; br_lt).
        mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0x5de574) F_1c55a4 eq_refl D_1c55a4);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_1c55a8 D_1c55a8 0x6a2760%Z C7 H8.
        mld F_1c55ac D_1c55ac kHighEnd C8 H8.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c55b0 eq_refl D_1c55b0)). gr.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c55b4 eq_refl D_1c55b4)). gr. rewrite H11, k_hse_val. unfold kHighBeg.
        replace (17594333495296 - 1)%Z with 17594333495295%Z by reflexivity.
        mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_1c55b8 eq_refl D_1c55b8); gr; unfold kHighEnd; br_lt).
        mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c55bc eq_refl D_1c55bc); gr; br_lt).
        apply mst_refl.
      + gr. split; [apply (f_equal (Z_to_bv 64)); lia|].
        intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blk_C : forall regs,
    getr regs 8 = Z_to_bv 64 beg -> getr regs 18 = Z_to_bv 64 en ->
    exists regs',
      msteps SEGS (mkst regs (0x1c0590 : word) m7 rom) (mkst regs' (0x1c05b0 : word) m7 rom)
      /\ getr regs' 19 = Z_to_bv 64 (SB + gu) /\ getr regs' 10 = Z_to_bv 64 (SB + ge)
      /\ (forall r, m2s_clob r = false -> r <> 1 -> r <> 19 -> r <> 20 -> getr regs' r = getr regs r).
  Proof.
    intros regs H8 H18.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM).
    evar (rr1 : bvmap 5 word).
    edestruct (mem_to_shadow rom rr1 m7 (gu * 8)%Z (0x1c05a4 : word) cells_m7) as (r1 & M1 & R1 & K1); cycle -1.
    { evar (rr2 : bvmap 5 word).
      edestruct (mem_to_shadow rom rr2 m7 (ge * 8)%Z (0x1c05b0 : word) cells_m7) as (r2 & M2 & R2 & K2); cycle -1.
      { rewrite Z.div_mul in R1 by lia. rewrite Z.div_mul in R2 by lia.
        exists r2. split; [|split; [|split]].
        - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c55c0 eq_refl D_1c55c0); gr; rewrite ?H8, ?H18; br_lt).
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c55c4 eq_refl D_1c55c4)). gr. rewrite H8. zn.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_1c55c8 eq_refl D_1c55c8)). gr. rewrite v_andi_m8 by lia.
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_1c55cc eq_refl D_1c55cc)). gr. rewrite H18, v_andi_m8 by lia.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_1c55d0 eq_refl D_1c55d0)). rewrite lit_83d10.
          eapply msteps_trans; [subst rr1; exact M1|].
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c55d4 eq_refl D_1c55d4)). rewrite R1. zn. rewrite Z.add_0_r.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c55d8 eq_refl D_1c55d8)). gr.
          rewrite (K1 20) by (reflexivity || discriminate). subst rr1. gr. zn. rewrite Z.add_0_r.
          mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_1c55dc eq_refl D_1c55dc)). rewrite lit_83d1c.
          subst rr2. exact M2.
        - subst rr1 rr2. rewrite (K2 19) by (reflexivity || discriminate). gr. reflexivity.
        - exact R2.
        - subst rr1 rr2. intros r Hr Hr1 Hr19 Hr20. unfold m2s_clob in Hr. rewrite (K2 r Hr).
          rewrite !getr_other by first [congruence | (intros ->; cbn in Hr; discriminate)].
          rewrite (K1 r Hr).
          rewrite !getr_other by first [congruence | (intros ->; cbn in Hr; discriminate)]. reflexivity. }
      all: subst rr1 rr2; gr; try reflexivity; try lia; try apply ret_ok_83d1c;
           try (unfold in_mem, kLowEnd, kHighBeg, kHighEnd; lia); try (apply (f_equal (Z_to_bv 64)); lia). }
    all: subst rr1; gr; try reflexivity; try lia; try apply ret_ok_83d10;
           try (unfold in_mem, kLowEnd, kHighBeg, kHighEnd; lia); try (apply (f_equal (Z_to_bv 64)); lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma g0_lt_g1 : (g0 < g1)%Z.
  Proof. pose proof divfacts. lia. Qed.

  Lemma shadow_beg : m7 (Z_to_bv 64 (SB + g0)) = Some (Z_to_bv 8 0).
  Proof.
    pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val. pose proof g0_lt_g1.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    rewrite m7_below by (rewrite zbv_u by lia; unfold g1, en in *; lia).
    apply (rp_zero _ _ _ _ _ H). unfold g0, g1, en in *. lia.
  Qed.

  Lemma shadow_last : m7 (Z_to_bv 64 (SB + g1)) = Some b1.
  Proof.
    pose proof (rp_disj _ _ _ _ _ H). pose proof divfacts. pose proof SB_val.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR.
    rewrite m7_below by (rewrite zbv_u by lia; unfold g1, en in *; lia).
    apply (rp_last _ _ _ _ _ H).
  Qed.

  Lemma v_lb_0 : v_lb (Z_to_bv 8 0) = Z_to_bv 64 0.
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.

  Definition d_clob (r : reg) : bool := (bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 18)%bool.

  Lemma blk_D : forall regs,
    getr regs 21 = Z_to_bv 64 0x6a1a78 -> getr regs 8 = Z_to_bv 64 beg -> getr regs 18 = Z_to_bv 64 en ->
    exists regs',
      msteps SEGS (mkst regs (0x1c05b0 : word) m7 rom) (mkst regs' (0x1c0620 : word) m7 rom)
      /\ (forall r, d_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H21 H8 H18.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM). pose proof g0_lt_g1 as Hg.
    pose proof cells_m7 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    pose proof (rp_b1 _ _ _ _ _ H) as Hb1. pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (Hrd0 : rdn SEGS m7 (Z_to_bv 64 (SB + beg / 8)) 1 = Some [Z_to_bv 8 0]) by (apply rdn1; apply shadow_beg).
    assert (Hrd1 : rdn SEGS m7 (Z_to_bv 64 (SB + (en - 1) / 8)) 1 = Some [b1]) by (apply rdn1; apply shadow_last).
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    destruct Hb1 as [Hz | Hpart].
    - (* [comment removed for export] *)
      eexists. split.
      + mld F_1c55e0 D_1c55e0 SB C2 H21.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c55e4 eq_refl D_1c55e4)). gr. rewrite H8, (v_srli_3 beg) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c55e8 eq_refl D_1c55e8)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_1c55ec eq_refl D_1c55ec);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd0).
        rewrite v_lb_0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_1c55f0 eq_refl D_1c55f0); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c55fc eq_refl D_1c55fc)). gr. rewrite H18. zn.
        replace (en + -1)%Z with (en - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c5600 eq_refl D_1c5600)). gr. rewrite (v_srli_3 (en - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c5604 eq_refl D_1c5604)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ b1 F_1c5608 eq_refl D_1c5608);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd1).
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_1c560c eq_refl D_1c560c); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros r Hr. unfold d_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - (* [comment removed for export] *)
      eexists. split.
      + mld F_1c55e0 D_1c55e0 SB C2 H21.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c55e4 eq_refl D_1c55e4)). gr. rewrite H8, (v_srli_3 beg) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c55e8 eq_refl D_1c55e8)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_1c55ec eq_refl D_1c55ec);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd0).
        rewrite v_lb_0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_1c55f0 eq_refl D_1c55f0); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c55fc eq_refl D_1c55fc)). gr. rewrite H18. zn.
        replace (en + -1)%Z with (en - 1)%Z by lia.
        mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_1c5600 eq_refl D_1c5600)). gr. rewrite (v_srli_3 (en - 1)) by lia.
        mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_1c5604 eq_refl D_1c5604)). gr. rewrite v_add_zbv by lia.
        mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ b1 F_1c5608 eq_refl D_1c5608);
                     gr; imm_norm; zn; rewrite Z.add_0_r; exact Hrd1).
        unfold v_lb. rewrite Hsg.
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_1c560c eq_refl D_1c560c); gr; rewrite ?getr_zero; br_eq).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_1c5610 eq_refl D_1c5610)). gr. rewrite v_andi_7 by lia.
        mstep ltac:(eapply (step_blt_tk _ _ _ _ _ _ _ _ _ F_1c5614 eq_refl D_1c5614); gr;
                     rewrite c_lts_zbv by lia; apply Z.ltb_lt; unfold en in *; lia).
        apply mst_refl.
      + intros r Hr. unfold d_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mz_pre : mzH m7 (SB + gu) (ge - gu) (usp - 64).
  Proof.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM). pose proof (rp_disj _ _ _ _ _ H) as Hdisj.
    pose proof (rp_b1 _ _ _ _ _ H) as Hb1.
    constructor.
    - unfold ge, gu, en in *. lia.
    - lia.
    - lia.
    - lia.
    - left. unfold g1, ge, en in *. lia.
    - intros i Hi. rewrite m7_below by (rewrite zbv_u by lia; unfold g1, ge, en in *; lia).
      destruct (Z.lt_ge_cases (gu + i) g1) as [Hlt | Hge'].
      + replace (SB + gu + i)%Z with (SB + (gu + i))%Z by lia. apply (rp_zero _ _ _ _ _ H). unfold g0, g1, gu, en in *. lia.
      + assert (Ei : (gu + i)%Z = g1) by (unfold g1, ge, en in *; lia).
        assert (Hz : bv_unsigned b1 = 0%Z) by (unfold g1, ge, en in *; lia).
        replace (SB + gu + i)%Z with (SB + g1)%Z by lia.
        unfold g1, en. rewrite (rp_last _ _ _ _ _ H). f_equal. apply bv_eq. rewrite Hz. reflexivity.
    - apply stk8; [lia | lia |]. intros x Hx. unfold m7. repeat apply store_ok1_wbytes. exact Hx.
  Qed.

  Definition e_clob (r : reg) : bool := (mz_clob r || bv_eqb r 1)%bool.

  Lemma blk_E : forall regs,
    getr regs 19 = Z_to_bv 64 (SB + gu) -> getr regs 10 = Z_to_bv 64 (SB + ge) -> getr regs 2 = Z_to_bv 64 (usp - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x1c0620 : word) m7 rom) (mkst regs' (0x1c0634 : word) m8 rom)
      /\ getr regs' 2 = Z_to_bv 64 (usp - 64)
      /\ (forall r, e_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H19 H10 H2.
    pose proof rng as HR. unfold kLowEnd, kHighBeg, kHighEnd in HR. pose proof SB_val as HSB.
    pose proof divfacts as (D0 & D1 & DU & DE & DM).
    evar (rr : bvmap 5 word).
    edestruct (as_mem_is_zero m7 rom (SB + gu) (ge - gu) (usp - 64) (0x1c0630 : word) mz_pre rr ret_ok_83d9c)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { exists r1. split; [|split].
      - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_1c5650 eq_refl D_1c5650); gr; rewrite ?H19, ?H10;
                     unfold ge, gu, en in *; br_lt).
        mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_1c5654 eq_refl D_1c5654)). gr. rewrite H10, H19, v_sub_zbv by lia.
        replace (SB + ge - (SB + gu))%Z with (ge - gu)%Z by lia.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5658 eq_refl D_1c5658)). gr. rewrite H19. zn. rewrite Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_1c565c eq_refl D_1c565c)). rewrite lit_83d9c.
        eapply msteps_trans; [subst rr; exact M1|].
        mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_1c5660 eq_refl D_1c5660); gr; rewrite ?R10, ?getr_zero; br_eq).
        unfold m8. replace (usp - 64 - 8)%Z with (usp - 72)%Z by lia. apply mst_refl.
      - exact R2.
      - subst rr. intros r Hr. unfold e_clob in Hr. apply orb_false_iff in Hr. destruct Hr as [Hr Hr1'].
        destruct (bv_eq_dec _ r 2) as [-> | Hr2].
        { rewrite R2. symmetry. exact H2. }
        rewrite (K1 r Hr Hr2) by (intros ->; cbn in Hr1'; discriminate).
        unfold mz_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr, Hr1'; discriminate)). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  Definition f_clob (r : reg) : bool :=
    (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 10 || bv_eqb r 18 || bv_eqb r 19
     || bv_eqb r 20 || bv_eqb r 21)%bool.

  Lemma blk_F : forall regs,
    getr regs 2 = Z_to_bv 64 (usp - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x1c0634 : word) m8 rom) (mkst regs' ra m8 rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H2.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5664 eq_refl D_1c5664)). rewrite getr_zero. zn. rewrite Z.add_0_r.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5668 eq_refl D_1c5668)). gr. zn. rewrite Z.add_0_r.
      mld2 F_1c566c D_1c566c ra RD1 H2.
      mld2 F_1c5670 D_1c5670 (getr regs0 8) RD8 H2.
      mld2 F_1c5674 D_1c5674 (getr regs0 9) RD9 H2.
      mld2 F_1c5678 D_1c5678 (getr regs0 18) RD18 H2.
      mld2 F_1c567c D_1c567c (getr regs0 19) RD19 H2.
      mld2 F_1c5680 D_1c5680 (getr regs0 20) RD20 H2.
      mld2 F_1c5684 D_1c5684 (getr regs0 21) RD21 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_1c5688 eq_refl D_1c5688)). gr. rewrite H2. zn.
      replace (usp - 64 + 64)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_1c568c eq_refl D_1c568c); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold f_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as_region_is_poisoned_RP :
    exists regs',
      msteps SEGS (mkst regs0 (0x1c04bc : word) mem rom) (mkst regs' ra m8 rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, rp_clob r = false -> getr regs' r = getr regs0 r).
  Proof.
    destruct blk_P as (q1 & MP & P2 & P8 & P9 & P1 & PK).
    destruct (blk_A q1 P8) as (q2 & MA & A21 & A11 & A12 & AK).
    assert (AK' : forall r, m2s_clob r = false -> r <> 21 -> getr q2 r = getr q1 r) by exact AK.
    destruct (blk_B q2) as (q3 & MB & B18 & BK);
      [rewrite AK by (reflexivity || discriminate); exact P8
      |rewrite AK by (reflexivity || discriminate); exact P9 | exact A11 | exact A12 |].
    destruct (blk_C q3) as (q4 & MC & C19 & C10 & CK);
      [rewrite BK, AK by (reflexivity || discriminate); exact P8 | exact B18 |].
    destruct (blk_D q4) as (q5 & MD & DK);
      [rewrite CK, BK by (reflexivity || discriminate); exact A21
      |rewrite CK, BK, AK by (reflexivity || discriminate); exact P8
      |rewrite CK by (reflexivity || discriminate); exact B18 |].
    destruct (blk_E q5) as (q6 & ME & E2 & EK);
      [rewrite DK by reflexivity; exact C19 | rewrite DK by reflexivity; exact C10
      |rewrite DK, CK, BK, AK by (reflexivity || discriminate); exact P2 |].
    destruct (blk_F q6 E2) as (q7 & MF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & FK).
    exists q7. split; [|split; [exact F10 | split; [exact F2 | split; [exact F1|]]]].
    - eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MA|]. eapply msteps_trans; [exact MB|].
      eapply msteps_trans; [exact MC|]. eapply msteps_trans; [exact MD|]. eapply msteps_trans; [exact ME|]. exact MF.
    - intros r Hr.
      destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite F1; symmetry; exact H01|].
      destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite F2; symmetry; exact H02|].
      destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact F8|].
      destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact F9|].
      destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact F18|].
      destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact F19|].
      destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact F20|].
      destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact F21|].
      assert (Hm2s : m2s_clob r = false) by exact Hr.
      unfold rp_clob in Hr.
      repeat match type of Hr with (?a || ?b)%bool = false =>
        apply orb_false_iff in Hr; destruct Hr as [Hr ?] end.
      Ltac clobside N1 N2 N8 N9 N18 N19 N20 N21 :=
        unfold f_clob, e_clob, d_clob, b_clob, mz_clob, m2s_clob;
        rewrite ?(bv_eqb_neq _ _ N1), ?(bv_eqb_neq _ _ N2), ?(bv_eqb_neq _ _ N8), ?(bv_eqb_neq _ _ N9),
                ?(bv_eqb_neq _ _ N18), ?(bv_eqb_neq _ _ N19), ?(bv_eqb_neq _ _ N20), ?(bv_eqb_neq _ _ N21);
        repeat match goal with H : bv_eqb _ _ = false |- _ => rewrite H end; reflexivity.
      rewrite FK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite EK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite DK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite CK by first [exact Hm2s | assumption].
      rewrite BK by clobside N1 N2 N8 N9 N18 N19 N20 N21.
      rewrite AK by first [exact Hm2s | assumption].
      apply PK. unfold rp_tmp, rp_clob.
      rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8), (bv_eqb_neq _ _ N9),
              (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20), (bv_eqb_neq _ _ N21).
      repeat match goal with H : bv_eqb r ?k = false |- _ => rewrite H end. reflexivity.
  Qed.
End RP.

(* [comment removed for export] *)
Theorem as_region_is_poisoned :
  forall (mem rom : word -> option byte) (beg n usp : Z) (b1 : byte),
  rpH mem beg n usp b1 ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x1c04bc : word) mem rom)
                (mkst regs' ra (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18)
                                              (getr regs 19) (getr regs 20) (getr regs 21)) rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, rp_clob r = false -> getr regs' r = getr regs r).
Proof.
  intros mem rom beg n usp b1 H regs ra Hret H1 H2 H10 H11.
  rewrite <- (m8_frame mem usp regs ra).
  exact (as_region_is_poisoned_RP mem rom beg n usp b1 H regs ra Hret H1 H2 H10 H11).
Qed.

(* [comment removed for export] *)
