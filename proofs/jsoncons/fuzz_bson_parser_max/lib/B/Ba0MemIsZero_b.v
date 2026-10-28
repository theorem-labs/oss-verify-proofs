(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r71700_717b4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_drop_low' : forall q r j i, (0 <= j)%Z -> (0 <= r < 2 ^ j)%Z -> (j <= i)%Z ->
  Z.testbit (q * 2 ^ j + r) i = Z.testbit (q * 2 ^ j) i.
Proof.
  intros q r j i Hj Hr Hi.
  replace i with ((i - j) + j)%Z by lia.
  rewrite <- !Z.div_pow2_bits by lia.
  f_equal. rewrite Z.div_add_l by lia. rewrite (Z.div_small r) by lia.
  rewrite Z_div_mult by lia. lia.
Qed.

Lemma testbit_m8 : forall i, (0 <= i)%Z -> Z.testbit (2 ^ 64 - 8) i = ((3 <=? i) && (i <? 64))%Z%bool.
Proof.
  intros i Hi.
  replace (2 ^ 64 - 8)%Z with ((2 ^ 61 - 1) * 2 ^ 3)%Z by reflexivity.
  destruct (Z.lt_ge_cases i 3) as [Hlt|Hge].
  - rewrite Z.mul_pow2_bits_low by lia. symmetry. apply andb_false_intro1. apply Z.leb_gt. lia.
  - rewrite Z.mul_pow2_bits by lia. replace (2 ^ 61 - 1)%Z with (Z.ones 61) by reflexivity.
    replace (3 <=? i)%Z with true by (symmetry; apply Z.leb_le; lia).
    destruct (Z.lt_ge_cases i 64) as [H64|H64].
    + rewrite Z.ones_spec_low by lia. symmetry. apply Z.ltb_lt. lia.
    + rewrite Z.ones_spec_high by lia. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma land_down8 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 8) = (x - x mod 8)%Z.
Proof.
  intros x Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
  set (q := (x / 8)%Z) in *. set (r := (x mod 8)%Z) in *.
  replace (x - r)%Z with (q * 2 ^ 3)%Z by lia.
  rewrite Hdm. replace (8 * q + r)%Z with (q * 2 ^ 3 + r)%Z by lia.
  assert (Hq : (0 <= q < 2 ^ 61)%Z) by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_m8 by lia.
  destruct (Z.lt_ge_cases i 3) as [Hlt|Hge].
  - replace (3 <=? i)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    rewrite andb_false_r. symmetry. apply Z.mul_pow2_bits_low. lia.
  - rewrite testbit_drop_low' by lia. replace (3 <=? i)%Z with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + replace (i <? 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). now rewrite andb_true_r.
    + replace (i <? 64)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      rewrite Z.mul_pow2_bits by lia. symmetry.
      destruct (Z.eq_dec q 0) as [->|Hq0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 61); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
(* [comment removed for export] *)
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
(* [comment removed for export] *)
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub; imm_norm; unorm; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
Definition kcs2 (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> r <> 2%bv -> getr regs' r = getr regs r.
#[using="Type"] Lemma kcs2_refl : forall regs, kcs2 regs regs.  Proof. intros regs r _ _. reflexivity. Qed.
#[using="Type"] Lemma kcs2_trans : forall r1 r2 r3, kcs2 r1 r2 -> kcs2 r2 r3 -> kcs2 r1 r3.
Proof. intros r1 r2 r3 A B r Hr H2. rewrite (B r Hr H2). apply A; assumption. Qed.
#[using="Type"] Lemma kcs2_upd : forall regs regs' (rd : reg) v,
  kcs2 regs regs' -> (~ In rd callee_saved \/ rd = 2%bv) -> kcs2 regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr H2. rewrite getr_other; [apply K; assumption|]. intros ->. destruct Hn as [Hn|Hn]; [exact (Hn Hr)|exact (H2 Hn)].
Qed.
#[using="Type"] Lemma kcs2_keeps_cs : forall regs regs' v, kcs2 regs regs' -> getr regs 2%bv = v -> keeps_cs regs (regupd regs' 2%bv v).
Proof.
  intros regs regs' v K Hv r Hr. destruct (decide (r = 2%bv)) as [->|Hne].
  - rewrite getr_same by (intro X; discriminate X). symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K; assumption.
Qed.
#[using="Type"] Lemma kcs2_upd_same : forall regs regs' (rd : reg) v,
  kcs2 regs regs' -> getr regs rd = v -> rd <> 0%bv -> kcs2 regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr H2. destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K; assumption.
Qed.
#[using="Type"] Lemma kcs2_to_keeps_cs : forall regs regs', kcs2 regs regs' -> getr regs' 2%bv = getr regs 2%bv -> keeps_cs regs regs'.
Proof.
  intros regs regs' K H2 r Hr. destruct (decide (r = 2%bv)) as [->|Hne]; [exact H2 | apply K; assumption].
Qed.
Ltac solve_kcs2 :=
  repeat (first [ apply kcs2_upd; [| first [right; reflexivity | left; not_kept] ]
                | apply kcs2_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply kcs2_refl | assumption].

Section Walk.
  Variable mem0 : word -> option byte.
  Variables beg sp ra : word.          (* [comment removed for export] *)
  Variables n b s e ab ae : Z.         (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Hypothesis Hb_def : bv_unsigned beg = b.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis He_def : e = (b + n)%Z.
  Hypothesis Hab_def : ab = (b + 7 - (b + 7) mod 8)%Z.   (* [comment removed for export] *)
  Hypothesis Hae_def : ae = (e - e mod 8)%Z.             (* [comment removed for export] *)
  Hypothesis Hn : (0 < n <= 2 ^ 40)%Z.
  Hypothesis He : (b + n + 8 < 2 ^ 64)%Z.
  Hypothesis Hs : (16 <= s)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hdisj : (b + n <= s - 8 \/ s <= b)%Z.     (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 8)) 8%nat = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HZ : forall x : word, (b <= bv_unsigned x < b + n)%Z -> mem0 x = Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  #[local] Notation M1 := (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (only parsing).

  #[using="beg Hb_def"] Lemma b_range : (0 <= b < 2 ^ 64)%Z.  Proof. rewrite <- Hb_def. apply u64_range. Qed.
  #[using="Hb_def"] Lemma beg_b : beg = Z_to_bv 64 b.  Proof. rewrite <- Hb_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[using="Hs_def"] Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[using="n s e He_def Hab_def Hn Hs"] Lemma ab_range : (b <= ab <= b + 7)%Z /\ (ab mod 8 = 0)%Z.
  Proof. rewrite Hab_def. pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)). pose proof (Z.div_mod (b+7) 8 ltac:(lia)).
         split; [lia|]. replace (b + 7 - (b + 7) mod 8)%Z with (8 * ((b + 7) / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
  #[using="beg n b s Hb_def He_def Hae_def Hn Hs"] Lemma ae_range : (Z.max 0 (e - 7) <= ae <= e)%Z /\ (ae mod 8 = 0)%Z.
  Proof. rewrite Hae_def. pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)). pose proof b_range.
         assert (0 <= e / 8)%Z by (apply Z.div_pos; lia).
         split; [lia|]. replace (e - e mod 8)%Z with (8 * (e / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

  #[using="beg e Hb_def He_def Hn Hs Hdisj HZ"] Lemma M1_zero : forall x : word, (b <= bv_unsigned x < b + n)%Z -> M1 x = Some (Z_to_bv 8 0).
  Proof.
    intros x Hx. pose proof b_range.
    destruct Hdisj as [Hd|Hd].
    - rewrite wbytes_below; [apply HZ; exact Hx | rewrite length_N_to_le_bytes; cbn [Z.of_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HZ; exact Hx | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.

  #[using="beg e Hb_def He_def Hn He Hs Hdisj HZ"] Lemma rdn1_M1 : forall z, (b <= z < b + n)%Z -> rdn ASEGS M1 (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    intros z Hz. pose proof b_range. cbn [rdn]. rewrite (M1_zero (Z_to_bv 64 z)) by (unorm; lia). reflexivity.
  Qed.

  #[using="beg e Hb_def He_def Hn He Hs Hdisj HZ"] Lemma rdn8_M1 : forall z, (b <= z)%Z -> (z + 8 <= b + n)%Z -> rdn ASEGS M1 (Z_to_bv 64 z) 8%nat = Some (repeat (Z_to_bv 8 0) 8%nat).
  Proof.
    intros z Hz1 Hz2. pose proof b_range. apply rdn_const; [cbn [Z.of_nat Pos.to_nat]; unorm; lia|].
    intros x Hx. apply M1_zero. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite u_Z2bv in Hx by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pro_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = beg /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 13 = Z_to_bv 64 n
    /\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.

  #[using="b Hb_def Hs_def He_def Hab_def Hae_def Hn He Hs Hdisj Hok"] Lemma pro_run : forall regs,
    getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst regs' (0x8b9dc : word) M1 rom)
      /\ pro_post regs' /\ kcs2 regs regs'.
  Proof.
    intros regs H10 H11 H2 H1. pose proof b_range as Hb. pose proof ab_range as Hab. pose proof ae_range as Hae.
    rewrite beg_b in H10. rewrite sp_s in H2.
    eexists. split.
    - stepiv F_8b594 D_8b594 (Z_to_bv 64 (s - 16)) ltac:(wval).   (* [comment removed for export] *)
      stepsd F_8b598 D_8b598 (Z_to_bv 64 (s - 8)) ra ltac:(exact Hok).                                             (* [comment removed for export] *)
      stepiv F_8b59c D_8b59c (Z_to_bv 64 n) ltac:(wval).         (* [comment removed for export] *)
      stepn F_8b5a0 D_8b5a0.                                                                                          (* [comment removed for export] *)
      stepn F_8b5a4 D_8b5a4.                                                                                          (* [comment removed for export] *)
      stepn F_8b5a8 D_8b5a8.                                                                                          (* [comment removed for export] *)
      stepb_ft F_8b5ac D_8b5ac ltac:(cond).                                                                           (* [comment removed for export] *)
      stepn F_8b5b0 D_8b5b0.                                                                                          (* [comment removed for export] *)
      stepiv F_8b5b4 D_8b5b4 (Z_to_bv 64 e) ltac:(rewrite He_def; wval).                                                (* [comment removed for export] *)
      stepiv F_8b5b8 D_8b5b8 (Z_to_bv 64 (b + 7)) ltac:(wval).                                          (* [comment removed for export] *)
      stepiv F_8b5bc D_8b5bc (Z_to_bv 64 ab)
        ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; rewrite Hab_def; reflexivity).  (* [comment removed for export] *)
      stepiv F_8b5c0 D_8b5c0 (Z_to_bv 64 ae)
        ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; rewrite Hae_def; reflexivity).  (* [comment removed for export] *)
      apply mst_refl.
    - split.
      + unfold pro_post. repeat split; gres; rwH; try reflexivity. symmetry; apply beg_b.
      + solve_kcs2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  (* [comment removed for export] *)
  #[local] Ltac mlbu0 F D z :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply rdn1_M1; lia]
      | step_simpl; vnorm].
  (* [comment removed for export] *)
  #[local] Ltac mld0 F D z :=
    chain_step; [reflexivity
      | eapply step_ld with (v := Z_to_bv 64 0); [exact F | reflexivity | exact D | maddr z; apply rdn8_M1; lia | reflexivity]
      | step_simpl; vnorm].
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_kcs2.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition l1_inv (rg : bvmap 5 word) (k : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (b + k + 1) /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab
    /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
  Definition l1_post (rg : bvmap 5 word) : Prop :=
    getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e /\ getr rg 15 = Z_to_bv 64 ab
    /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.

  #[using="beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop1_run : forall (q : nat) regs k,
    l1_inv regs k -> (0 <= k)%Z -> (k + Z.of_nat q + 1 = Z.min ab e - b)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b9ec : word) M1 rom) (mkst regs' (0x8ba04 : word) M1 rom)
      /\ l1_post regs' /\ kcs2 regs regs'.
  Proof.
    induction q as [|q IH]; intros regs k (H13 & H11 & H14 & H15 & H12 & H10 & H2 & H1) Hk Hq;
      pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    - (* [comment removed for export] *)
      destruct (Z.le_gt_cases ab e) as [Hle|Hgt].
      + (* [comment removed for export] *)
        eexists. split.
        * stepiv F_8b5d4 D_8b5d4 (Z_to_bv 64 (b + k + 1)) ltac:(wval).      (* [comment removed for export] *)
          mlbu0 F_8b5d8 D_8b5d8 (b + k)%Z.                                   (* [comment removed for export] *)
          stepn F_8b5dc D_8b5dc.                                             (* [comment removed for export] *)
          stepb_tk F_8b5e0 D_8b5e0 ltac:(cond).                              (* [comment removed for export] *)
          apply mst_refl.
        * unfold l1_post. post.
      + (* [comment removed for export] *)
        eexists. split.
        * stepiv F_8b5d4 D_8b5d4 (Z_to_bv 64 (b + k + 1)) ltac:(wval).
          mlbu0 F_8b5d8 D_8b5d8 (b + k)%Z.
          stepn F_8b5dc D_8b5dc.
          stepb_ft F_8b5e0 D_8b5e0 ltac:(cond).                              (* [comment removed for export] *)
          stepiv F_8b5e4 D_8b5e4 (Z_to_bv 64 (b + k + 2)) ltac:(wval).      (* [comment removed for export] *)
          stepb_ft F_8b5e8 D_8b5e8 ltac:(cond).                              (* [comment removed for export] *)
          apply mst_refl.
        * unfold l1_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b9ec : word) M1 rom) (fun rg => l1_inv rg (k + 1) /\ kcs2 regs rg)).
      + eexists. split.
        * stepiv F_8b5d4 D_8b5d4 (Z_to_bv 64 (b + k + 1)) ltac:(wval).
          mlbu0 F_8b5d8 D_8b5d8 (b + k)%Z.
          stepn F_8b5dc D_8b5dc.
          stepb_ft F_8b5e0 D_8b5e0 ltac:(cond).                              (* [comment removed for export] *)
          stepiv F_8b5e4 D_8b5e4 (Z_to_bv 64 (b + k + 2)) ltac:(wval).      (* [comment removed for export] *)
          stepb_tk F_8b5e8 D_8b5e8 ltac:(cond).                              (* [comment removed for export] *)
          apply mst_refl.
        * unfold l1_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (k + 1)%Z I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition l2_inv (rg : bvmap 5 word) (j : Z) : Prop :=
    getr rg 15 = Z_to_bv 64 (ab + 8 * j) /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
    /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
  Definition l2_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 ae /\ getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
    /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.

  #[using="beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop2_run : forall (q : nat) regs j,
    l2_inv regs j -> (0 <= j)%Z -> (ab + 8 * (j + Z.of_nat q + 1) = ae)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8ba08 : word) M1 rom) (mkst regs' (0x8ba18 : word) M1 rom)
      /\ l2_post regs' /\ kcs2 regs regs'.
  Proof.
    induction q as [|q IH]; intros regs j (H15 & H11 & H14 & H12 & H10 & H2 & H1) Hj Hq;
      pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    - eexists. split.
      + mld0 F_8b5f0 D_8b5f0 (ab + 8 * j)%Z.                                 (* [comment removed for export] *)
        stepiv F_8b5f4 D_8b5f4 (Z_to_bv 64 (ab + 8 * (j + 1))) ltac:(wval).  (* [comment removed for export] *)
        stepn F_8b5f8 D_8b5f8.                                               (* [comment removed for export] *)
        stepb_ft F_8b5fc D_8b5fc ltac:(cond).                                (* [comment removed for export] *)
        apply mst_refl.
      + unfold l2_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8ba08 : word) M1 rom) (fun rg => l2_inv rg (j + 1) /\ kcs2 regs rg)).
      + eexists. split.
        * mld0 F_8b5f0 D_8b5f0 (ab + 8 * j)%Z.
          stepiv F_8b5f4 D_8b5f4 (Z_to_bv 64 (ab + 8 * (j + 1))) ltac:(wval).
          stepn F_8b5f8 D_8b5f8.
          stepb_tk F_8b5fc D_8b5fc ltac:(cond).                              (* [comment removed for export] *)
          apply mst_refl.
        * unfold l2_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (j + 1)%Z I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition l3_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 12 = Z_to_bv 64 (ae + i) /\ getr rg 14 = Z_to_bv 64 (e - ae - i) /\ getr rg 11 = Z_to_bv 64 0
    /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.
  Definition l3_post (rg : bvmap 5 word) : Prop :=
    getr rg 11 = Z_to_bv 64 0 /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.

  #[using="beg n ab Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma loop3_run : forall (q : nat) regs i,
    l3_inv regs i -> (0 <= i)%Z -> (ae + i + Z.of_nat q + 1 = e)%Z -> (b <= ae)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x8ba24 : word) M1 rom) (mkst regs' (0x8ba38 : word) M1 rom)
      /\ l3_post regs' /\ kcs2 regs regs'.
  Proof.
    induction q as [|q IH]; intros regs i (H12 & H14 & H11 & H2 & H1) Hi Hq Hbae;
      pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    - eexists. split.
      + mlbu0 F_8b60c D_8b60c (ae + i)%Z.                                    (* [comment removed for export] *)
        stepiv F_8b610 D_8b610 (Z_to_bv 64 (e - ae - (i + 1))) ltac:(wval).  (* [comment removed for export] *)
        stepn F_8b614 D_8b614.                                               (* [comment removed for export] *)
        stepiv F_8b618 D_8b618 (Z_to_bv 64 (ae + (i + 1))) ltac:(wval).      (* [comment removed for export] *)
        stepb_ft F_8b61c D_8b61c ltac:(cond).                                (* [comment removed for export] *)
        apply mst_refl.
      + unfold l3_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8ba24 : word) M1 rom) (fun rg => l3_inv rg (i + 1) /\ kcs2 regs rg)).
      + eexists. split.
        * mlbu0 F_8b60c D_8b60c (ae + i)%Z.
          stepiv F_8b610 D_8b610 (Z_to_bv 64 (e - ae - (i + 1))) ltac:(wval).
          stepn F_8b614 D_8b614.
          stepiv F_8b618 D_8b618 (Z_to_bv 64 (ae + (i + 1))) ltac:(wval).
          stepb_tk F_8b61c D_8b61c ltac:(cond).                              (* [comment removed for export] *)
          apply mst_refl.
        * unfold l3_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z I1 ltac:(lia) ltac:(lia) Hbae) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="beg b e Hb_def Hs_def Hs Hret"] Lemma epi_run : forall regs,
    l3_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x8ba38 : word) M1 rom) (mkst regs' ra M1 rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ kcs2 regs regs'.
  Proof.
    intros regs (H11 & H2 & H1). pose proof b_range as Hb.
    eexists. split.
    - stepiv F_8b620 D_8b620 (Z_to_bv 64 1) ltac:(gres; rwH; reflexivity).                       (* [comment removed for export] *)
      stepld F_8b624 D_8b624 ra ltac:(maddr (s - 8)%Z; apply rdn_wbytes_hit8; unorm; lia).        (* [comment removed for export] *)
      stepiv F_8b628 D_8b628 (Z_to_bv 64 s) ltac:(wval).                                           (* [comment removed for export] *)
      stepret F_8b62c D_8b62c ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - post. all: try (symmetry; apply sp_s). all: solve_kcs2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mid_post (rg : bvmap 5 word) : Prop :=
    getr rg 11 = Z_to_bv 64 0 /\ getr rg 14 = Z_to_bv 64 e
    /\ getr rg 12 = Z_to_bv 64 ae /\ getr rg 10 = Z_to_bv 64 b /\ getr rg 2 = Z_to_bv 64 (s - 16) /\ getr rg 1 = ra.

  #[using="beg n Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma mid_run : forall regs,
    l1_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x8ba04 : word) M1 rom) (mkst regs' (0x8ba18 : word) M1 rom)
      /\ mid_post regs' /\ kcs2 regs regs'.
  Proof.
    intros regs (H11 & H14 & H15 & H12 & H10 & H2 & H1).
    pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    destruct (Z.le_gt_cases ae ab) as [Hskip|Hgo].
    - eexists. split.
      + stepb_tk F_8b5ec D_8b5ec ltac:(cond).                               (* [comment removed for export] *)
        apply mst_refl.
      + unfold mid_post. post.
    - assert (Hq : exists q : nat, (ab + 8 * (0 + Z.of_nat q + 1) = ae)%Z).
      { destruct Hab as [Hab1 Hab2]. destruct Hae as [Hae1 Hae2].
        pose proof (Z.div_mod ab 8 ltac:(lia)) as Dab. pose proof (Z.div_mod ae 8 ltac:(lia)) as Dae.
        rewrite Hab2 in Dab. rewrite Hae2 in Dae.
        exists (Z.to_nat (ae / 8 - ab / 8 - 1)). rewrite Z2Nat.id; lia. }
      destruct Hq as (q & Hq).
      eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8ba08 : word) M1 rom) (fun rg => l2_inv rg 0 /\ kcs2 regs rg)).
      + eexists. split.
        * stepb_ft F_8b5ec D_8b5ec ltac:(cond).                             (* [comment removed for export] *)
          apply mst_refl.
        * unfold l2_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (loop2_run q r1 0 I1 ltac:(lia) Hq) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN|]. split; [|eapply kcs2_trans; eassumption].
        destruct P2 as (Q15 & Q11 & Q14 & Q12 & Q10 & Q2 & Q1). unfold mid_post. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="beg n ab Hb_def He_def Hab_def Hae_def Hn He Hs Hdisj HZ"] Lemma tail_run : forall regs,
    mid_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x8ba18 : word) M1 rom) (mkst regs' (0x8ba38 : word) M1 rom)
      /\ l3_post regs' /\ kcs2 regs regs'.
  Proof.
    intros regs (H11 & H14 & H12 & H10 & H2 & H1).
    pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    destruct (Z.lt_ge_cases ae b) as [Hlow|Hhigh].
    - eexists. split.
      + stepb_tk F_8b600 D_8b600 ltac:(cond).                               (* [comment removed for export] *)
        apply mst_refl.
      + unfold l3_post. post.
    - destruct (Z.le_gt_cases e ae) as [Hskip|Hgo].
      + eexists. split.
        * stepb_ft F_8b600 D_8b600 ltac:(cond).                             (* [comment removed for export] *)
          stepb_tk F_8b604 D_8b604 ltac:(cond).                             (* [comment removed for export] *)
          apply mst_refl.
        * unfold l3_post. post.
      + assert (Hq : exists q : nat, (ae + 0 + Z.of_nat q + 1 = e)%Z) by (exists (Z.to_nat (e - ae - 1)); rewrite Z2Nat.id; lia).
        destruct Hq as (q & Hq).
        eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8ba24 : word) M1 rom) (fun rg => l3_inv rg 0 /\ kcs2 regs rg)).
        * eexists. split.
          -- stepb_ft F_8b600 D_8b600 ltac:(cond).                          (* [comment removed for export] *)
             stepb_ft F_8b604 D_8b604 ltac:(cond).                          (* [comment removed for export] *)
             stepiv F_8b608 D_8b608 (Z_to_bv 64 (e - ae - 0)) ltac:(wval).  (* [comment removed for export] *)
             apply mst_refl.
          -- unfold l3_inv. post.
        * cbv beta. intros r1 (I1 & K1).
          destruct (loop3_run q r1 0 I1 ltac:(lia) Hq Hhigh) as (r2 & RUN & P2 & K2).
          exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="b e ab ae Hb_def Hs_def He_def Hab_def Hae_def Hn He Hs Hdisj Hok Hret HZ"] Theorem mem_is_zero_run : forall regs,
    getr regs 10 = beg -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst regs' ra M1 rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H2 H1.
    pose proof b_range as Hb; pose proof ab_range as Hab; pose proof ae_range as Hae.
    (* [comment removed for export] *)
    assert (STEP : forall (pcA pcB : word) (PA PB : bvmap 5 word -> Prop),
              (exists r1, msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst r1 pcA M1 rom) /\ (PA r1 /\ kcs2 regs r1)) ->
              (forall r1, PA r1 -> exists r2, msteps ASEGS (mkst r1 pcA M1 rom) (mkst r2 pcB M1 rom) /\ PB r2 /\ kcs2 r1 r2) ->
              exists r2, msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst r2 pcB M1 rom) /\ (PB r2 /\ kcs2 regs r2)).
    { intros pcA pcB PA PB HA HB.
      eapply (runs_trans ASEGS _ (fun rg => mkst rg pcA M1 rom) (fun rg => PA rg /\ kcs2 regs rg)); [exact HA|].
      cbv beta. intros r1 (P1 & K1). destruct (HB r1 P1) as (r2 & RUN & P2 & K2).
      exists r2. split; [exact RUN | split; [exact P2 | eapply kcs2_trans; eassumption]]. }
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst r1 (0x8b9dc : word) M1 rom) /\ (pro_post r1 /\ kcs2 regs r1)).
    { destruct (pro_run regs H10 H11 H2 H1) as (r1 & RUN & P & K). exists r1. split; [exact RUN | split; assumption]. }
    (* [comment removed for export] *)
    assert (S2 : exists r1, msteps ASEGS (mkst regs (0x8b9ac : word) mem0 rom) (mkst r1 (0x8ba04 : word) M1 rom) /\ (l1_post r1 /\ kcs2 regs r1)).
    { apply (STEP (0x8b9dc : word) (0x8ba04 : word) pro_post l1_post S1).
      intros r1 (P10 & P11 & P12 & P13 & P14 & P15 & P2 & P1). rewrite beg_b in P10.
      destruct (Z.le_gt_cases ab b) as [Hal|Hunal].
      - (* [comment removed for export] *)
        eexists. split.
        + stepb_tk F_8b5c4 D_8b5c4 ltac:(cond).
          apply mst_refl.
        + unfold l1_post. post.
      - (* [comment removed for export] *)
        assert (Hq : exists q : nat, (0 + Z.of_nat q + 1 = Z.min ab e - b)%Z) by (exists (Z.to_nat (Z.min ab e - b - 1)); rewrite Z2Nat.id; lia).
        destruct Hq as (q & Hq).
        eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x8b9ec : word) M1 rom) (fun rg => l1_inv rg 0 /\ kcs2 r1 rg)).
        + eexists. split.
          * stepb_ft F_8b5c4 D_8b5c4 ltac:(cond).                               (* [comment removed for export] *)
            stepb_ft F_8b5c8 D_8b5c8 ltac:(cond).                               (* [comment removed for export] *)
            stepn F_8b5cc D_8b5cc.                                              (* [comment removed for export] *)
            stepiv F_8b5d0 D_8b5d0 (Z_to_bv 64 (b + 0 + 1)) ltac:(wval).       (* [comment removed for export] *)
            apply mst_refl.
          * unfold l1_inv. post.
        + cbv beta. intros r2 (I2 & K2).
          destruct (loop1_run q r2 0 I2 ltac:(lia) Hq) as (r3 & RUN & P3 & K3).
          exists r3. split; [exact RUN | split; [exact P3 | eapply kcs2_trans; eassumption]]. }
    (* [comment removed for export] *)
    pose proof (STEP _ _ _ _ S2 mid_run) as S3.
    pose proof (STEP _ _ _ _ S3 tail_run) as S4.
    destruct S4 as (r4 & RUN4 & P4 & K4).
    destruct (epi_run r4 P4) as (r5 & RUN5 & Q10 & Q2 & Q1 & K5).
    exists r5. split; [eapply msteps_trans; [exact RUN4 | exact RUN5]|].
    repeat split; try assumption.
    apply kcs2_to_keeps_cs; [eapply kcs2_trans; eassumption | rewrite Q2, H2; reflexivity].
  Qed.
End Walk. End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
