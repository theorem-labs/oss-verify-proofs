(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit MemsetLib As0StepLib Pm8MemIsZero Pm8RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8SumsMemset_code Pm8SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_7f000_80000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Lemma lxor_ones64 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.lxor a (2 ^ 64 - 1) = (2 ^ 64 - 1 - a)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 1 - a)%Z with ((Z.lnot a) mod 2 ^ 64)%Z.
  2:{ unfold Z.lnot. replace (Z.pred (- a)) with ((2 ^ 64 - 1 - a) + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
    apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
    rewrite (Z.bits_above_log2 a i); [reflexivity| lia |].
    assert (Z.log2 a < 64)%Z; [|lia].
    destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
    apply Z.log2_lt_pow2; lia.
Qed.

Lemma land255_small : forall a, (0 <= a < 256)%Z -> Z.land a 255 = a.
Proof. intros a Ha. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma lor_bound64 : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (0 <= Z.lor a b < 2 ^ 64)%Z.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hl : (Z.log2 (Z.lor a b) < 64)%Z).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
  assert (Hnn : (0 <= Z.lor a b)%Z) by (apply Z.lor_nonneg; lia).
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma zbv_wrap_up : forall z, Z_to_bv 64 z = Z_to_bv 64 (z + 2 ^ 64).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  replace (z + 2 ^ 64)%Z with (z + 1 * 2 ^ 64)%Z by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma bytes8_range : forall segs M (a : word) bs, rdn segs M a 8%nat = Some bs -> (0 <= bytes_le_to_Z bs < 2 ^ 64)%Z.
Proof.
  intros segs M a bs H. pose proof (rdn_length _ _ _ _ _ H) as L. pose proof (bytes_le_to_Z_bound bs) as B.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B. lia.
Qed.

Definition memb (r : reg) (L : list reg) : bool := existsb (fun x => bv_eqb x r) L.
Lemma memb_true : forall r L, memb r L = true -> In r L.
Proof.
  intros r L H. unfold memb in H. apply existsb_exists in H. destruct H as (x & Hx & E).
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst x. exact Hx.
Qed.
Lemma memb_false : forall r L, memb r L = false -> ~ In r L.
Proof.
  intros r L H Hin. unfold memb in H.
  assert (T : existsb (fun x => bv_eqb x r) L = true) by (apply existsb_exists; exists r; split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]).
  rewrite T in H. discriminate.
Qed.
Lemma keeps_but_updb : forall L regs regs' (rd : reg) v,
  keeps_but L regs regs' -> (memb rd L || negb (memb rd callee_saved))%bool = true -> keeps_but L regs (regupd regs' rd v).
Proof.
  intros L regs regs' rd v K Hb. apply keeps_but_upd; [exact K|].
  destruct (memb rd L) eqn:E1; [left; apply memb_true; exact E1|].
  destruct (memb rd callee_saved) eqn:E2; [cbn in Hb; discriminate|]. right. apply memb_false. exact E2.
Qed.
Ltac solve_keeps_but :=
  repeat (apply keeps_but_updb; [| reflexivity ]);
  first [apply keeps_but_refl | assumption | apply keeps_but_cs; assumption].

Section FPX_0. Context {fx : PropExec.FPState}.

Lemma step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_slt_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_slt (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_slt segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_sltu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros * Hf He Hd Hrd Hv. rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
End FPX_0.

Ltac stepov F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Op ALU_OR _ _ _, _) => eapply step_or_at with (v := vv)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) => eapply step_and_at with (v := vv)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) => eapply step_slt_at with (v := vv)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) => eapply step_sltu_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section FPX_1. Context {fx : PropExec.FPState}.

Definition ms_icpt_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x153ca0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15d699)) /\
  rdn ASEGS M (0x15d699 : word) 1%nat = Some [Z_to_bv 8 1] /\
  rdn ASEGS M (0x155160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x145308)).

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.

Section AMS.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra cv : word.
  Variables p n s kL f l fa la : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hf_def : f = (SB + p / 8)%Z.
  Hypothesis Hl_def : l = (SB + (p + n - 1) / 8)%Z.
  Hypothesis Hfa_def : fa = (f - f mod 8)%Z.
  Hypothesis Hla_def : la = (l - l mod 8)%Z.
  Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
  Hypothesis Happ : (0 <= p /\ p + n + 8 <= LOWEND)%Z \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND)%Z.
  Hypothesis Hs : (0x1000000 <= s - 2200)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hshs : (l + 8 <= s - 2200)%Z.
  Hypothesis Hdisj : (0 < n -> p + n <= s - 2200 \/ s <= p)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2200)) 2200%nat = true.
  Hypothesis Hdst : store_ok ASEGS mem0 (Z_to_bv 64 p) (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HI : ms_icpt_globs mem0.
  Hypothesis HZ : (0 < n)%Z -> forall x : word, (f <= bv_unsigned x < l)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HL : (0 < n)%Z -> mem0 (Z_to_bv 64 l) = Some (Z_to_bv 8 kL).
  Hypothesis HkL : kL = 0%Z \/ ((p + n - 1) mod 8 < kL <= 7)%Z.
  Hypothesis HW : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 fa) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 la) 8%nat = Some w1.

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma p_facts : (0 <= p)%Z /\ (p + n + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (0 < n -> p / 8 <= (p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.

  Definition out_agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 2200 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma out_agree_refl : out_agree mem0.  Proof. intros x _. reflexivity. Qed.
  Lemma out_agree_w : forall M k v, out_agree M -> (8 <= k <= 2200)%Z -> out_agree (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)).
  Proof.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma out_agree_rdn : forall M (a : word) k, out_agree M -> (bv_unsigned a + Z.of_nat k <= s - 2200)%Z ->
    rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  Lemma out_agree_globs : forall M, out_agree M -> rt_layout_globs M /\ ms_icpt_globs M.
  Proof.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3).
    unfold rt_layout_globs, ms_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  Lemma out_agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 2200)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2200)) _ 2200%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.

  Definition M8 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)).
  Lemma M8_out_agree : forall rg, out_agree (M8 rg).  Proof. intros rg. unfold M8. oagree. Qed.
  Lemma M8_grows : forall rg, mem_grows mem0 (M8 rg).  Proof. intros rg. unfold M8. grows. Qed.

  Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)).
  Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.

  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
  Lemma M8_FR : forall regs0, FR regs0 (M8 regs0).
  Proof. intros regs0. split; [apply M8_out_agree | split; [apply M8_grows|]]. unfold M8. repeat split; slot. Qed.

  Definition c1_post (regs rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 2 = Z_to_bv 64 (s - 2128) /\ getr rg 1 = ra.

  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f310 : word) mem0 rom) (mkst regs' (0x7f348 : word) (M8 regs) rom)
      /\ c1_post regs regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H12 H2 H1. rewrite sp_s in H2.
    pose proof (out_agree_globs (M8 regs) (M8_out_agree regs)) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & (I1 & I2 & I3)).
    unfold M8 in *.
    eexists. split.
    - stepiv F_7f2c0 D_7f2c0 (Z_to_bv 64 (s - 2032)) ltac:(wval).
      stepsd F_7f2c4 D_7f2c4 (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
      stepsd F_7f2c8 D_7f2c8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
      stepsd F_7f2cc D_7f2cc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
      stepsd F_7f2d0 D_7f2d0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
      stepsd F_7f2d4 D_7f2d4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
      stepsd F_7f2d8 D_7f2d8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
      stepsd F_7f2dc D_7f2dc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
      stepiv F_7f2e0 D_7f2e0 (Z_to_bv 64 s) ltac:(wval).
      stepiv F_7f2e4 D_7f2e4 (Z_to_bv 64 (s - 2128)) ltac:(wval).
      stepn F_7f2e8 D_7f2e8.
      mld F_7f2ec D_7f2ec (0x153ca0 : word) I1.
      mlbu F_7f2f0 D_7f2f0 (0x15d699 : word) I2.
      stepb_ft F_7f2f4 D_7f2f4 ltac:(cond).
      apply mst_refl.
    - unfold c1_post. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
  Qed.

  Definition c2_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).

  #[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
  Lemma ret_ok_5e5c8 : ret_ok (0x7f4f8 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma c2z_run : forall regs0 regs,
    c1_post regs0 regs -> n = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f348 : word) (M8 regs0) rom) (mkst regs' (0x7f3a0 : word) (M8 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H10 & H11 & H12 & H8 & H2 & H1) Hn0. pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold HIGHEND in *.
    eexists. split.
    - stepiv F_7f2f8 D_7f2f8 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepiv F_7f2fc D_7f2fc (Z_to_bv 64 (s - 2048)) ltac:(wval).
      stepiv F_7f300 D_7f300 (Z_to_bv 64 (s - 2128)) ltac:(wval).
      stepb_ft F_7f304 D_7f304 ltac:(cond).
      stepiv F_7f308 D_7f308 (Z_to_bv 64 (2 ^ 64 - 65))
        ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_7f30c D_7f30c.
      stepb_tk F_7f310 D_7f310 ltac:(cond).
      stepb_ft F_7f458 D_7f458 ltac:(cond).
      stepn F_7f45c D_7f45c.
      apply mst_refl.
    - unfold c2_post. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  Lemma rdn_slot_ext : forall (M1 M2 : word -> option byte) k,
    (forall x : word, (s - 2128 <= bv_unsigned x < s)%Z -> M1 x = M2 x) -> (8 <= k <= 2128)%Z ->
    rdn ASEGS M1 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat.
  Proof.
    intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
  Qed.
  Lemma slots_ok_ext : forall regs0 (M1 M2 : word -> option byte),
    (forall x : word, (s - 2128 <= bv_unsigned x < s)%Z -> M2 x = M1 x) -> slots_ok regs0 M1 -> slots_ok regs0 M2.
  Proof.
    intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold slots_ok.
    rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
  Qed.
  Lemma FR_region : forall regs0 M', frame_only (M8 regs0) (s - 2128) M' -> mem_grows (M8 regs0) M' -> FR regs0 M'.
  Proof.
    intros regs0 M' HF HGr. pose proof (M8_FR regs0) as (O8 & G8 & R8).
    split; [|split].
    - intros x Hx. rewrite (HF x) by lia. apply O8. exact Hx.
    - eapply mem_grows_trans; [exact G8 | exact HGr].
    - apply (slots_ok_ext regs0 (M8 regs0) M'); [|exact R8]. intros x Hx. apply HF. lia.
  Qed.

  Lemma c2r_run : forall regs0 regs,
    c1_post regs0 regs -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7f348 : word) (M8 regs0) rom) (mkst regs' (0x7f3a0 : word) M' rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    intros regs0 regs (H10 & H11 & H12 & H8 & H2 & H1) Hn64. pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
    unfold HIGHEND in *.

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x7f348 : word) (M8 regs0) rom) (mkst r1 (0x826a0 : word) (M8 regs0) rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ getr r1 1 = (0x7f4f8 : word)
                  /\ getr r1 9 = Z_to_bv 64 p /\ getr r1 21 = cv /\ getr r1 18 = Z_to_bv 64 n /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_7f2f8 D_7f2f8 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepiv F_7f2fc D_7f2fc (Z_to_bv 64 (s - 2048)) ltac:(wval).
        stepiv F_7f300 D_7f300 (Z_to_bv 64 (s - 2128)) ltac:(wval).
        stepb_ft F_7f304 D_7f304 ltac:(cond).
        stepiv F_7f308 D_7f308 (Z_to_bv 64 (n - 65)) ltac:(wval).
        stepn F_7f30c D_7f30c.
        stepb_tk F_7f310 D_7f310 ltac:(cond).
        stepb_tk F_7f458 D_7f458 ltac:(cond).
        stepiv F_7f494 D_7f494 (Z_to_bv 64 p) ltac:(wval).
        stepiv F_7f498 D_7f498 cv ltac:(gres; rwH; apply v_addi_0).
        stepiv F_7f49c D_7f49c (Z_to_bv 64 n) ltac:(wval).
        stepiv F_7f4a0 D_7f4a0 (Z_to_bv 64 n) ltac:(wval).
        stepn F_7f4a4 D_7f4a4.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q9 & Q21 & Q18 & K1).
    pose proof (out_agree_globs (M8 regs0) (M8_out_agree regs0)) as (HG8 & _).
    pose proof (region_is_poisoned_run (M8 regs0) rom (Z_to_bv 64 (s - 2128)) (0x7f4f8 : word) p n (s - 2128)
                  ltac:(unorm; reflexivity) ltac:(lia) Happ ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2128 - 72)%Z with (s - 2200)%Z by lia; apply out_agree_store_ok; [apply M8_grows | cbn; lia])
                  ret_ok_5e5c8 HG8 kL) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (M8_out_agree regs0 x) by (unfold SB in *; lia); apply HZ; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite (M8_out_agree regs0) by (unfold SB in *; unorm; lia); rewrite <- Hl_def; apply HL; lia) HkL).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
    assert (S21 : getr r2 21 = cv) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    eexists. exists M2. split; [|split; [|split; [|apply FR_region; assumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_7f4a8 D_7f4a8 cv ltac:(gres; rwH; apply v_addi_0).
      stepiv F_7f4ac D_7f4ac (Z_to_bv 64 n) ltac:(wval).
      stepiv F_7f4b0 D_7f4b0 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_7f4b4 D_7f4b4 (Z_to_bv 64 p) ltac:(wval).
      stepb_tk F_7f4b8 D_7f4b8 ltac:(cond).
      apply mst_refl.
    - unfold c2_post. repeat split; gres; rwH; reflexivity.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Lemma fl_facts : (0 < n)%Z -> (SB <= f <= l)%Z /\ (l + 8 <= s - 2200)%Z /\ (f - 7 <= fa <= f)%Z /\ (l - 7 <= la <= l)%Z
                               /\ (fa mod 8 = 0)%Z /\ (la mod 8 = 0)%Z.
  Proof.
    intros Hn0. pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound f 8 ltac:(lia)). pose proof (Z.mod_pos_bound l 8 ltac:(lia)).
    pose proof (Z.div_mod f 8 ltac:(lia)). pose proof (Z.div_mod l 8 ltac:(lia)).
    repeat split; try lia.
    - rewrite Hfa_def. replace (f - f mod 8)%Z with (8 * (f / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult.
    - rewrite Hla_def. replace (l - l mod 8)%Z with (8 * (l / 8))%Z by lia. rewrite Z.mul_comm. apply Z_mod_mult.
  Qed.

  Lemma rdnW_M8 : forall regs0, (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS (M8 regs0) (Z_to_bv 64 fa) 8%nat = Some w0 /\ rdn ASEGS (M8 regs0) (Z_to_bv 64 la) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    intros regs0 Hn64. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6). unfold SB in *.
    destruct (HW Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn (M8 regs0)) by (first [apply M8_out_agree | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  Lemma rdn1_M8 : forall regs0 z, (0 < n)%Z -> (f <= z < l)%Z -> rdn ASEGS (M8 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    intros regs0 z Hn0 Hz. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite (M8_out_agree regs0) by (unorm; lia). rewrite (HZ Hn0) by (unorm; lia). reflexivity.
  Qed.
  Lemma rdnL_M8 : forall regs0 z, (0 < n)%Z -> z = l -> rdn ASEGS (M8 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kL].
  Proof.
    intros regs0 z Hn0 ->. pose proof (fl_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite (M8_out_agree regs0) by (unorm; lia). rewrite (HL Hn0). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlbu0 F D z :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply rdn1_M8; lia]
      | step_simpl; vnorm].
  #[local] Ltac mlbk F D z :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdnL_M8; lia]
      | step_simpl; vnorm; rewrite (v_lb_k kL ltac:(lia))].

  #[local] Ltac mldw F D z R w :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
      | step_simpl; vnorm].

  Definition c2qa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 13 = Z_to_bv 64 f /\ getr rg 14 = Z_to_bv 64 l /\ getr rg 15 = Z_to_bv 64 (p + n - 1) /\ getr rg 16 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).

  Lemma c2qa_run : forall regs0 regs w0 w1,
    c1_post regs0 regs -> (0 < n <= 64)%Z ->
    rdn ASEGS (M8 regs0) (Z_to_bv 64 fa) 8%nat = Some w0 -> rdn ASEGS (M8 regs0) (Z_to_bv 64 la) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f348 : word) (M8 regs0) rom) (mkst regs' (0x7f39c : word) (M8 regs0) rom)
      /\ c2qa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs w0 w1 (H10 & H11 & H12 & H8 & H2 & H1) Hn64 R0 R1 B0 B1.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
    pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof (out_agree_globs (M8 regs0) (M8_out_agree regs0)) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound f 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound l 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_7f2f8 D_7f2f8 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepiv F_7f2fc D_7f2fc (Z_to_bv 64 (s - 2048)) ltac:(wval).
      stepiv F_7f300 D_7f300 (Z_to_bv 64 (s - 2128)) ltac:(wval).
      stepb_ft F_7f304 D_7f304 ltac:(cond).
      stepiv F_7f308 D_7f308 (Z_to_bv 64 (2 ^ 64 + n - 65))
        ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (n + - 65)); f_equal; lia).
      stepn F_7f30c D_7f30c.
      stepb_ft F_7f310 D_7f310 ltac:(cond).
      stepn F_7f314 D_7f314.
      mld F_7f318 D_7f318 (0x153138 : word) G1.
      stepiv F_7f31c D_7f31c (Z_to_bv 64 (p + n)) ltac:(wval).
      mld F_7f320 D_7f320 (0x15c9b8 : word) G2.
      stepiv F_7f324 D_7f324 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_7f328 D_7f328 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
      stepiv F_7f32c D_7f32c (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
      stepiv F_7f330 D_7f330 (Z_to_bv 64 f) ltac:(wval).
      stepiv F_7f334 D_7f334 (Z_to_bv 64 l) ltac:(wval).
      stepiv F_7f338 D_7f338 (Z_to_bv 64 fa)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_7f33c D_7f33c (Z_to_bv 64 la)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_7f340 D_7f340 fa R0 w0.
      mldw F_7f344 D_7f344 la R1 w1.
      stepov F_7f348 D_7f348 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold c2qa_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
  Qed.

  Definition ql_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 13 = Z_to_bv 64 (f + i) /\ getr rg 14 = Z_to_bv 64 l /\ getr rg 15 = Z_to_bv 64 0
    /\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  Definition ql_post (rg : bvmap 5 word) : Prop :=
    getr rg 15 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 p /\ getr rg 11 = cv /\ getr rg 12 = Z_to_bv 64 n /\ getr rg 2 = Z_to_bv 64 (s - 2128).
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
  #[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.

  Lemma qloop_run : forall regs0 (q : nat) regs i,
    (0 < n)%Z -> ql_inv regs i -> (0 <= i)%Z -> (f + i + Z.of_nat q + 1 = l)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f4cc : word) (M8 regs0) rom) (mkst regs' (0x7f4dc : word) (M8 regs0) rom)
      /\ ql_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 q. induction q as [|q IH]; intros regs i Hn0 (H13 & H14 & H15 & H10 & H11 & H12 & H2) Hi Hq;
      pose proof (fl_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_7f47c D_7f47c (f + i)%Z.
        stepiv F_7f480 D_7f480 (Z_to_bv 64 (f + i + 1)) ltac:(wval).
        stepov F_7f484 D_7f484 (Z_to_bv 64 0) ltac:(vlit).
        stepb_ft F_7f488 D_7f488 ltac:(cond).
        apply mst_refl.
      + unfold ql_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7f4cc : word) (M8 regs0) rom) (fun rg => ql_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_7f47c D_7f47c (f + i)%Z.
          stepiv F_7f480 D_7f480 (Z_to_bv 64 (f + i + 1)) ltac:(wval).
          stepov F_7f484 D_7f484 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_7f488 D_7f488 ltac:(cond).
          apply mst_refl.
        * unfold ql_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  Lemma c2qf_run : forall regs0 regs u0 u1,
    c2qa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f39c : word) (M8 regs0) rom) (mkst regs' (0x7f3a0 : word) (M8 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs u0 u1 (H13 & H14 & H15 & H16 & H10 & H11 & H12 & H2) BL E.
    eexists. split.
    - stepb_ft F_7f34c D_7f34c ltac:(cond).
      apply mst_refl.
    - unfold c2_post. post.
  Qed.

  Lemma c2qs_run : forall regs0 regs u0 u1,
    c2qa_post u0 u1 regs -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f39c : word) (M8 regs0) rom) (mkst regs' (0x7f3a0 : word) (M8 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs u0 u1 (H13 & H14 & H15 & H16 & H10 & H11 & H12 & H2) Hn64 BL NE.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)).
    pose proof (fl_facts ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.

    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7f4c8 : word) (M8 regs0) rom) (fun rg => ql_inv rg 0 /\ keeps_but RIPL regs rg)).
    { destruct HkL as [K0|K7].
      - eexists. split.
        + stepb_tk F_7f34c D_7f34c ltac:(cond).
          mlbk F_7f460 D_7f460 l.
          stepiv F_7f464 D_7f464 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_7f468 D_7f468 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kL)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_7f46c D_7f46c (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kL)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_7f470 D_7f470 (Z_to_bv 64 1) ltac:(vlit).
          stepov F_7f474 D_7f474 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold ql_inv. post.
      - eexists. split.
        + stepb_tk F_7f34c D_7f34c ltac:(cond).
          mlbk F_7f460 D_7f460 l.
          stepiv F_7f464 D_7f464 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_7f468 D_7f468 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kL)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_7f46c D_7f46c (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kL)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_7f470 D_7f470 (Z_to_bv 64 0) ltac:(vlit).
          stepov F_7f474 D_7f474 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold ql_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I10 & I11 & I12 & I2) & K1).

    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7f4dc : word) (M8 regs0) rom) (fun rg => ql_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases f l) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7f4cc : word) (M8 regs0) rom) (fun rg => ql_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_7f478 D_7f478 ltac:(cond).
            apply mst_refl.
          * split; [unfold ql_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloop_run regs0 (Z.to_nat (l - f - 1)) r2 0 ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_7f478 D_7f478 ltac:(cond).
          apply mst_refl.
        + split; [unfold ql_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J10 & J11 & J12 & J2) & K4).
    eexists. split.
    - stepiv F_7f48c D_7f48c (Z_to_bv 64 0) ltac:(vlit).
      stepb_tk F_7f490 D_7f490 ltac:(cond).
      apply mst_refl.
    - unfold c2_post. split; [repeat split; gres; rwH; reflexivity|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  Lemma c2_run : forall regs0 regs,
    c1_post regs0 regs ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7f348 : word) (M8 regs0) rom) (mkst regs' (0x7f3a0 : word) M' rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    intros regs0 regs P1.
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { destruct (c2z_run regs0 regs P1 Hn0) as (r2 & RUN2 & P2 & K2). exists r2, (M8 regs0).
      split; [exact RUN2 | split; [exact P2 | split; [exact K2 | apply M8_FR]]]. }
    destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
    - destruct (rdnW_M8 regs0 ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
      destruct (c2qa_run regs0 regs w0 w1 P1 ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
      pose proof (lor_bound64 _ _ B1 B0) as BL.
      destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
      + destruct (c2qf_run regs0 r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, (M8 regs0).
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | apply M8_FR]]].
      + destruct (c2qs_run regs0 r2 _ _ P2 ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, (M8 regs0).
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | apply M8_FR]]].
    - exact (c2r_run regs0 regs P1 Hgt).
  Qed.

  Lemma ret_ok_5e47c : ret_ok (0x7f3ac : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma keeps_but_ms : forall L r1 r2, ms_agree r1 r2 -> keeps_but L r1 r2.
  Proof. intros L r1 r2 AG. apply keeps_but_cs. apply keeps_keeps_cs. apply ms_agree_keeps. exact AG. Qed.

  #[local] Notation MS M := (wbytes M (Z_to_bv 64 p) (repeat (cbyte cv) (Z.to_nat n))) (only parsing).

  Lemma slots_ok_ms : forall regs0 M, slots_ok regs0 M -> slots_ok regs0 (wbytes M (Z_to_bv 64 p) (repeat (cbyte cv) (Z.to_nat n))).
  Proof.
    intros regs0 M R. pose proof p_facts as (Pp & Ppn & _). unfold HIGHEND in *.
    apply (slots_ok_ext regs0 M); [|exact R]. intros x Hx. pose proof (u64_range x).
    destruct (Z_lt_le_dec 0 n) as [Np|Nz]; [| first [ rewrite (proj1 (length_zero_iff_nil bs) ltac:(lia)); reflexivity | replace (Z.to_nat n) with 0%nat by lia; reflexivity ] ].
    destruct (Hdisj Np) as [Hd|Hd].
    - apply wbytes_above. rewrite repeat_length. unorm. lia.
    - apply wbytes_below; [rewrite repeat_length; unorm; lia | unorm; lia].
  Qed.

  Lemma c3_run : forall regs0 regs M,
    c2_post regs -> FR regs0 M ->
    exists regs',
      msteps ASEGS (mkst regs (0x7f3a0 : word) M rom) (mkst regs' ra (wbytes M (Z_to_bv 64 p) (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs M (H10 & H11 & H12 & H2) (HO & HGr & HR).
    pose proof p_facts as (Pp & Ppn & _). unfold HIGHEND in *.
    pose proof (out_agree_globs M HO) as (_ & (I1 & I2 & I3)).

    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x7f3a0 : word) M rom) (mkst r1 (0x145308 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = cv /\ getr r1 12 = Z_to_bv 64 n /\ getr r1 1 = (0x7f3ac : word)
                  /\ getr r1 2 = Z_to_bv 64 (s - 2128) /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepn F_7f350 D_7f350.
        mld F_7f354 D_7f354 (0x155160 : word) I3.
        stepjr F_7f358 D_7f358 (Z_to_bv 64 0x145308) ltac:(gres; reflexivity).
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q2 & K1).
    replace (0x145308 : word) with (Z_to_bv 64 ms_base) in RUN1 by (apply bv_eq; vm_compute; reflexivity).
    pose proof (memset_summary M (Z_to_bv 64 p) cv (0x7f3ac : word) n rom ltac:(lia) ltac:(unorm; lia)
                  ltac:(apply (store_ok_mono _ _ mem0 M _ HGr); exact Hdst) ret_ok_5e47c r1 Q10 Q11 Q12 Q1) as (r2 & RUN2 & V10 & AG).
    pose proof (slots_ok_ms regs0 M HR) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2128)) by (rewrite (ms_agree_getr _ _ 2%bv AG) by (cbv; intuition discriminate); exact Q2).
    assert (V1 : getr r2 1 = (0x7f3ac : word)) by (rewrite (ms_agree_getr _ _ 1%bv AG) by (cbv; intuition discriminate); exact Q1).
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_7f35c D_7f35c (Z_to_bv 64 (s - 2032)) ltac:(wval).
      stepld F_7f360 D_7f360 ra ltac:(maddr (s - 8)%Z; exact R1).
      stepld F_7f364 D_7f364 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
      stepld F_7f368 D_7f368 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
      stepld F_7f36c D_7f36c (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
      stepld F_7f370 D_7f370 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
      stepld F_7f374 D_7f374 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
      stepld F_7f378 D_7f378 (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
      stepiv F_7f37c D_7f37c (Z_to_bv 64 s) ltac:(wval).
      stepret F_7f380 D_7f380 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [exact V10 | symmetry; apply sp_s |].
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_ms; exact AG|]. solve_keeps_but.
  Qed.

  Theorem asan_memset_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x7f310 : word) mem0 rom) (mkst regs' ra (wbytes Mj (Z_to_bv 64 p) (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree Mj /\ mem_grows mem0 Mj.
  Proof.
    intros regs H10 H11 H12 H2 H1.
    destruct (c1_run regs H10 H11 H12 H2 H1) as (r1 & RUN1 & P1 & K1).
    destruct (c2_run regs r1 P1) as (r2 & M2 & RUN2 & P2 & K2 & F2).
    destruct (c3_run regs r2 M2 P2 F2) as (r3 & RUN3 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K3).
    exists r3, M2. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - assert (KB : keeps_but RIPL regs r3).
      { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K3. }
      destruct F2 as (HO & HGr & _).
      repeat split; try assumption.
      intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
      destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
      destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
      destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
      destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
      apply KB; [exact Hr|]. cbv. intuition congruence.
  Qed.

End AMS.
End FPX_1.
