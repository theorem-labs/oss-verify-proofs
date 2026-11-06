(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ea0MemIsZero Ea0RegionPoisoned Ea0AsanMemset Ea0AsanMemcpy Ea0DiagStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r50950_509ec Ea0_code_r50c28_50c30 Ea0_code_r4f2d8_4f480 Ea0_code_r4de14_4df90.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

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
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac aval := gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia.

Lemma rdn_zeros : forall (m : word -> option byte) n (a : word),
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some (Z_to_bv 8 0)) ->
  rdn ASEGS m a n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros m n; induction n as [|n IH]; intros a Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned. change (bv_unsigned (1 : word)) with 1%Z. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (u64_range a). apply Z.mod_small. lia. }
    rewrite (IH (a + 1)%bv); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia. apply Hall. lia.
Qed.

#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldw F D z R w :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
    | step_simpl; vnorm].

Section CHK.
  Variable M rom : word -> option byte.
  Variables p N s : Z.
  Hypothesis HN : (0 < N <= 2 ^ 40)%Z.
  Hypothesis Happ : in_app8 p N.
  Hypothesis Hp0 : (0 < p)%Z.
  Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hsh : (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z.
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true.
  Hypothesis HG : rt_layout_globs M.

  Hypothesis HZ : forall x : word, (SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + N - 1) / 8 + 8) (SB + 2 ^ 44))%Z -> M x = Some (Z_to_bv 8 0).

  Variables fS lS faS laS : Z.
  Hypothesis HfS_def : fS = (SB + p / 8)%Z.           Hypothesis HlS_def : lS = (SB + (p + N - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.

  Lemma p_facts : (0 <= p)%Z /\ (p + N + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (p / 8 <= (p + N - 1) / 8 <= 2 ^ 44 - 1)%Z.
  Proof.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
  Qed.
  Lemma fl_facts : (SB <= fS <= lS)%Z /\ (fS - 7 <= faS <= fS)%Z /\ (lS - 7 <= laS <= lS)%Z /\ (lS + 8 <= s - 72)%Z /\ (faS + 8 <= SB + 2 ^ 44)%Z /\ (laS + 8 <= SB + 2 ^ 44)%Z.
  Proof.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)).
    pose proof (Z.div_mod fS 8 ltac:(lia)). pose proof (Z.div_mod lS 8 ltac:(lia)). repeat split; lia.
  Qed.
  Lemma zero_word : forall a, (fS - 7 <= a)%Z -> (a <= lS)%Z -> (a + 8 <= SB + 2 ^ 44)%Z -> rdn ASEGS M (Z_to_bv 64 a) 8%nat = Some (repeat (Z_to_bv 8 0) 8).
  Proof.
    intros a Ha Hb Hc. pose proof fl_facts as (F1 & _ & _ & F5). pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    apply rdn_zeros; [unorm; cbn; lia|].
    intros i Hi. unorm. apply HZ. unfold SB. cbn in Hi. unorm. lia.
  Qed.

  Lemma ret_ok_67e7c : ret_ok (0x67ecc : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma chk1_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p ->
    exists regs',
      msteps ASEGS (mkst regs (0x67e38 : word) M rom) (mkst regs' (0x67d98 : word) M rom)
      /\ keeps_but [23]%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H22.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepiv F_67de8 D_67de8 (Z_to_bv 64 N) ltac:(wval).
      stepiv F_67dec D_67dec (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepb_ft F_67df0 D_67df0 ltac:(cond).
      stepiv F_67df4 D_67df4 (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
      stepn F_67df8 D_67df8.
      stepb_ft F_67dfc D_67dfc ltac:(cond).
      stepn F_67e00 D_67e00.
      mld F_67e04 D_67e04 (0x1391b8 : word) G1.
      stepiv F_67e08 D_67e08 (Z_to_bv 64 (p + N)) ltac:(wval).
      mld F_67e0c D_67e0c (0x1419f8 : word) G2.
      stepiv F_67e10 D_67e10 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_67e14 D_67e14 (Z_to_bv 64 (p + N - 1)) ltac:(wval).
      stepiv F_67e18 D_67e18 (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
      stepiv F_67e1c D_67e1c (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_67e20 D_67e20 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_67e24 D_67e24 (Z_to_bv 64 faS) ltac:(aval).
      stepiv F_67e28 D_67e28 (Z_to_bv 64 laS) ltac:(aval).
      mldw F_67e2c D_67e2c faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
      mldw F_67e30 D_67e30 laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
      stepov F_67e34 D_67e34 (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
      stepb_tk F_67e38 D_67e38 ltac:(cond).
      apply mst_refl.
    - solve_keeps_but.
  Qed.

  Definition frame72 (M' : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M' x = M x) /\ mem_grows M M'.
  Lemma frame72_refl : frame72 M.  Proof. split; [intros x _; reflexivity | apply mem_grows_refl]. Qed.

  Lemma region_call : forall regs (ra : word), (64 < N)%Z -> ret_ok ra ->
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 N -> getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7be44 : word) M rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ keeps_cs regs regs' /\ frame72 M'.
  Proof.
    intros regs ra Hn64 Hret H10 H11 H2 H1.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5). unfold SB, HIGHEND in *.
    destruct (region_is_poisoned_run M rom (Z_to_bv 64 s) ra p N s ltac:(unorm; reflexivity) HN Happ Hs ltac:(unfold SB; lia) Hok Hret HG 0%Z
                ltac:(intros x Hx; apply HZ; unfold SB in *; lia)
                ltac:(apply HZ; unfold SB in *; unorm; lia)
                ltac:(left; reflexivity) regs H10 H11 H2 H1) as (r2 & M2 & RUN & V10 & V2 & V1 & K2 & FO & GR).
    exists r2, M2. split; [exact RUN | split; [exact V10 | split; [exact K2 | split; [exact FO | exact GR]]]].
  Qed.

  Lemma chk1_region : forall regs, (64 < N)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x67e38 : word) M rom) (mkst regs' (0x67d98 : word) M' rom)
      /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H22 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x67e38 : word) M rom) (mkst r1 (0x7be44 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x67ecc : word) /\ keeps_but [1; 23]%bv regs r1)).
    { eexists. split.
      - stepiv F_67de8 D_67de8 (Z_to_bv 64 N) ltac:(wval).
        stepiv F_67dec D_67dec (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepb_ft F_67df0 D_67df0 ltac:(cond).
        stepiv F_67df4 D_67df4 (Z_to_bv 64 (N - 65)) ltac:(wval).
        stepn F_67df8 D_67df8.
        stepb_tk F_67dfc D_67dfc ltac:(cond).
        stepb_tk F_680bc D_680bc ltac:(cond).
        stepiv F_67e70 D_67e70 (Z_to_bv 64 p) ltac:(wval).
        stepiv F_67e74 D_67e74 (Z_to_bv 64 N) ltac:(wval).
        stepn F_67e78 D_67e78.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
    destruct (region_call r1 (0x67ecc : word) Hn64 ret_ok_67e7c Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    eexists. exists M2. split; [|split; [|exact FR2]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepb_tk F_67e7c D_67e7c ltac:(cond).
      apply mst_refl.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Theorem chk1_run : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x67e38 : word) M rom) (mkst regs' (0x67d98 : word) M' rom)
      /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs H10 H22 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
    - destruct (chk1_fast regs Hle H10 H22) as (r & RUN & K). exists r, M. split; [exact RUN | split; [|exact frame72_refl]].
      intros x Hx Hn. apply K; [exact Hx|]. intros [E|[]]. apply Hn. right. left. exact E.
    - apply chk1_region; [lia | assumption..].
  Qed.

  Lemma ret_ok_65b4c : ret_ok (0x65b9c : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma chk2_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps ASEGS (mkst regs (0x65a04 : word) M rom) (mkst regs' (0x65a64 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [9; 20]%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H18 H20.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepb_ft F_659b4 D_659b4 ltac:(cond).
      stepb_tk F_659b8 D_659b8 ltac:(cond).
      stepiv F_65a70 D_65a70 (Z_to_bv 64 (N - 1)) ltac:(wval).
      stepiv F_65a74 D_65a74 (Z_to_bv 64 N) ltac:(wval).
      stepiv F_65a78 D_65a78 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepn F_65a7c D_65a7c.
      stepn F_65a80 D_65a80.
      stepb_tk F_65a84 D_65a84 ltac:(cond).
      stepiv F_659cc D_659cc (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
      stepn F_659d0 D_659d0.
      stepb_ft F_659d4 D_659d4 ltac:(cond).
      stepn F_659d8 D_659d8.
      mld F_659dc D_659dc (0x1391b8 : word) G1.
      stepiv F_659e0 D_659e0 (Z_to_bv 64 (p + N)) ltac:(wval).
      mld F_659e4 D_659e4 (0x1419f8 : word) G2.
      stepiv F_659e8 D_659e8 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_659ec D_659ec (Z_to_bv 64 (p + N - 1)) ltac:(wval).
      stepiv F_659f0 D_659f0 (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
      stepiv F_659f4 D_659f4 (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_659f8 D_659f8 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_659fc D_659fc (Z_to_bv 64 faS) ltac:(aval).
      stepiv F_65a00 D_65a00 (Z_to_bv 64 laS) ltac:(aval).
      mldw F_65a04 D_65a04 faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
      mldw F_65a08 D_65a08 laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
      stepov F_65a0c D_65a0c (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
      stepb_ft F_65a10 D_65a10 ltac:(cond).
      apply mst_refl.
    - split; [gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  Lemma chk2_region : forall regs, (64 < N)%Z ->
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x65a04 : word) M rom) (mkst regs' (0x65a64 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H18 H20 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x65a04 : word) M rom) (mkst r1 (0x7be44 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x65b9c : word)
                  /\ getr r1 21 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs r1)).
    { eexists. split.
      - stepb_ft F_659b4 D_659b4 ltac:(cond).
        stepb_tk F_659b8 D_659b8 ltac:(cond).
        stepiv F_65a70 D_65a70 (Z_to_bv 64 (N - 1)) ltac:(wval).
        stepiv F_65a74 D_65a74 (Z_to_bv 64 N) ltac:(wval).
        stepiv F_65a78 D_65a78 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepn F_65a7c D_65a7c.
        stepn F_65a80 D_65a80.
        stepb_tk F_65a84 D_65a84 ltac:(cond).
        stepiv F_659cc D_659cc (Z_to_bv 64 (N - 65)) ltac:(wval).
        stepn F_659d0 D_659d0.
        stepb_tk F_659d4 D_659d4 ltac:(cond).
        stepb_tk F_65b00 D_65b00 ltac:(cond).
        stepiv F_65b3c D_65b3c (Z_to_bv 64 (p + N - 1)) ltac:(wval).
        stepiv F_65b40 D_65b40 (Z_to_bv 64 p) ltac:(wval).
        stepiv F_65b44 D_65b44 (Z_to_bv 64 N) ltac:(wval).
        stepn F_65b48 D_65b48.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & K1).
    destruct (region_call r1 (0x65b9c : word) Hn64 ret_ok_65b4c Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    assert (S21 : getr r2 21 = Z_to_bv 64 (p + N - 1)) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_65b4c D_65b4c (Z_to_bv 64 0) ltac:(wval).
      stepiv F_65b50 D_65b50 (Z_to_bv 64 (p + N - 1)) ltac:(wval).
      stepb_tk F_65b54 D_65b54 ltac:(cond).
      apply mst_refl.
    - gres; rwH; reflexivity.
    - eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
  Qed.

  Theorem chk2_run : forall regs,
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x65a04 : word) M rom) (mkst regs' (0x65a64 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs H10 H18 H20 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
    - destruct (chk2_fast regs Hle H10 H18 H20) as (r & RUN & V & K). exists r, M. split; [exact RUN | split; [exact V | split; [|exact frame72_refl]]].
      intros x Hx Hn. apply K; [exact Hx|]. intros [E|[E|[]]]; apply Hn; subst x; cbv; tauto.
    - apply chk2_region; [lia | assumption..].
  Qed.

  Lemma ret_ok_641d8 : ret_ok (0x64228 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Variable maxlen : Z.
  Hypothesis Hmax : (N < maxlen < 2 ^ 63)%Z.
  Hypothesis HFL : rdn ASEGS M (0x1391a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d3528)).
  Hypothesis HRS : rdn ASEGS M (0x1d3623 : word) 1%nat = Some [Z_to_bv 8 1].

  Lemma chk3_head : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen ->
    exists regs',
      msteps ASEGS (mkst regs (0x640b8 : word) M rom) (mkst regs' (0x640e4 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ getr regs' 9 = Z_to_bv 64 N /\ getr regs' 18 = Z_to_bv 64 p /\ getr regs' 2 = getr regs 2
      /\ keeps_but [9; 20; 21]%bv regs regs'.
  Proof.
    intros regs H10 H9 H18 H19.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    eexists. split.
    - stepb_ft F_64068 D_64068 ltac:(cond).
      stepn F_6406c D_6406c.
      mld F_64070 D_64070 (0x1391a8 : word) HFL.
      mlbu F_64074 D_64074 (0x1d3623 : word) HRS.
      stepb_ft F_64078 D_64078 ltac:(cond).
      stepiv F_6407c D_6407c (Z_to_bv 64 N) ltac:(wval).
      stepb_ft F_64080 D_64080 ltac:(cond).
      stepiv F_64084 D_64084 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepn F_64088 D_64088.
      stepn F_6408c D_6408c.
      stepb_ft F_64090 D_64090 ltac:(cond).
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
  Qed.

  Lemma chk3_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 N -> getr regs 18 = Z_to_bv 64 p ->
    exists regs',
      msteps ASEGS (mkst regs (0x640e4 : word) M rom) (mkst regs' (0x6412c : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but []%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H9 H18.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepiv F_64094 D_64094 (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).
      stepn F_64098 D_64098.
      stepb_ft F_6409c D_6409c ltac:(cond).
      stepn F_640a0 D_640a0.
      mld F_640a4 D_640a4 (0x1391b8 : word) G1.
      stepiv F_640a8 D_640a8 (Z_to_bv 64 (p + N)) ltac:(wval).
      mld F_640ac D_640ac (0x1419f8 : word) G2.
      stepiv F_640b0 D_640b0 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_640b4 D_640b4 (Z_to_bv 64 (p + N - 1)) ltac:(wval).
      stepiv F_640b8 D_640b8 (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
      stepiv F_640bc D_640bc (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_640c0 D_640c0 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_640c4 D_640c4 (Z_to_bv 64 faS) ltac:(aval).
      stepiv F_640c8 D_640c8 (Z_to_bv 64 laS) ltac:(aval).
      mldw F_640cc D_640cc faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
      mldw F_640d0 D_640d0 laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
      stepov F_640d4 D_640d4 (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
      stepb_ft F_640d8 D_640d8 ltac:(cond).
      apply mst_refl.
    - split; [gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  Lemma chk3_region : forall regs, (64 < N)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 N -> getr regs 18 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x640e4 : word) M rom) (mkst regs' (0x6412c : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 18; 22]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H9 H18 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x640e4 : word) M rom) (mkst r1 (0x7be44 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x64228 : word)
                  /\ getr r1 22 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 18; 22]%bv regs r1)).
    { eexists. split.
      - stepiv F_64094 D_64094 (Z_to_bv 64 (N - 65)) ltac:(wval).
        stepn F_64098 D_64098.
        stepb_tk F_6409c D_6409c ltac:(cond).
        stepb_tk F_6418c D_6418c ltac:(cond).
        stepiv F_641c8 D_641c8 (Z_to_bv 64 (N - 1)) ltac:(wval).
        stepiv F_641cc D_641cc (Z_to_bv 64 p) ltac:(wval).
        stepiv F_641d0 D_641d0 (Z_to_bv 64 N) ltac:(wval).
        stepn F_641d4 D_641d4.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q22 & K1).
    destruct (region_call r1 (0x64228 : word) Hn64 ret_ok_641d8 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    assert (S22 : getr r2 22 = Z_to_bv 64 (N - 1)) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
    eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_641d8 D_641d8 (Z_to_bv 64 0) ltac:(wval).
      stepiv F_641dc D_641dc (Z_to_bv 64 (N - 1)) ltac:(wval).
      stepb_tk F_641e0 D_641e0 ltac:(cond).
      apply mst_refl.
    - gres; rwH; reflexivity.
    - eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
  Qed.

  Theorem chk3_run : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x640b8 : word) M rom) (mkst regs' (0x6412c : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 9; 18; 20; 21; 22]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs H10 H9 H18 H19 H2.
    destruct (chk3_head regs H10 H9 H18 H19) as (r0 & RUN0 & A10 & A9 & A18 & A2 & K0). rewrite H2 in A2.
    assert (KW : forall L r r', keeps_but L r r' -> incl L [1; 9; 18; 20; 21; 22]%bv -> keeps_but [1; 9; 18; 20; 21; 22]%bv r r').
    { intros L r r' K I x Hx Hn. apply K; [exact Hx|]. intros Hin. apply Hn. apply I. exact Hin. }
    destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
    - destruct (chk3_fast r0 Hle A10 A9 A18) as (r & RUN & V & K). exists r, M.
      split; [eapply msteps_trans; [exact RUN0 | exact RUN] | split; [exact V | split; [|exact frame72_refl]]].
      eapply keeps_but_trans; [apply (KW _ _ _ K0) | apply (KW _ _ _ K)]; intros x Hx; cbn in Hx |- *; tauto.
    - destruct (chk3_region r0 ltac:(lia) A10 A9 A18 A2) as (r & M' & RUN & V & K & FR). exists r, M'.
      split; [eapply msteps_trans; [exact RUN0 | exact RUN] | split; [exact V | split; [|exact FR]]].
      eapply keeps_but_trans; [apply (KW _ _ _ K0) | apply (KW _ _ _ K)]; intros x Hx; cbn in Hx |- *; tauto.
  Qed.
End CHK.

Definition chk_pre (M : word -> option byte) (p N s : Z) : Prop :=
  (0 < N <= 2 ^ 40)%Z /\ in_app8 p N /\ (0 < p)%Z /\ ((0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z) /\ (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z
  /\ store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true /\ rt_layout_globs M
  /\ (forall x : word, (SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + N - 1) / 8 + 8) (SB + 2 ^ 44))%Z -> M x = Some (Z_to_bv 8 0)).

Theorem chk1 : forall M rom p N s regs, chk_pre M p N s ->
  getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x67e38 : word) M rom) (mkst regs' (0x67d98 : word) M' rom)
    /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (chk1_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk2 : forall M rom p N s regs, chk_pre M p N s ->
  getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x65a04 : word) M rom) (mkst regs' (0x65a64 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (chk2_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk3 : forall M rom p N s maxlen regs, chk_pre M p N s -> (N < maxlen < 2 ^ 63)%Z ->
  rdn ASEGS M (0x1391a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d3528)) -> rdn ASEGS M (0x1d3623 : word) 1%nat = Some [Z_to_bv 8 1] ->
  getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x640b8 : word) M rom) (mkst regs' (0x6412c : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 9; 18; 20; 21; 22]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s maxlen regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) B1 B2 B3.
  exact (chk3_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl maxlen B1 B2 B3 regs).
Qed.

Lemma ret_ok_67de8 : ret_ok (0x67e38 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Theorem strlen_chk1 : forall M rom p s (bs : list byte) regs,
  rdn ASEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]) ->
  (forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z) ->
  chk_pre M p (Z.of_nat (length bs) + 1) s ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x67e34 : word) M rom) (mkst regs' (0x67d98 : word) M' rom)
    /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p s bs regs HS HNZ CP H10 H22 H2.
  assert (Hp : (0 <= p)%Z /\ (p + Z.of_nat (length bs) + 1 < 2 ^ 63)%Z).
  { destruct CP as (_ & A2 & _). unfold in_app8, LOWEND, HIGHBEG, HIGHEND in A2. lia. }
  assert (S1 : exists r1, msteps ASEGS (mkst regs (0x67e34 : word) M rom) (mkst r1 (0x8bf38 : word) M rom)
            /\ (getr r1 1 = (0x67e38 : word) /\ getr r1 10 = Z_to_bv 64 p /\ getr r1 22 = Z_to_bv 64 p /\ getr r1 2 = Z_to_bv 64 s /\ keeps_but [1; 23]%bv regs r1)).
  { eexists. split.
    + stepn F_67de4 D_67de4. apply mst_refl.
    + repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
  destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & R2 & K1).
  {
    destruct (internal_strlen_run M rom p bs Hp HS HNZ r1 (0x67e38 : word) ret_ok_67de8 R1 R10) as (r2 & RUN2 & V10 & K2).
    assert (S22 : getr r2 22 = Z_to_bv 64 p) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
    assert (S2 : getr r2 2 = Z_to_bv 64 s) by (rewrite (K2 2%bv) by (cbv; tauto); exact R2).
    destruct (chk1 M rom p (Z.of_nat (length bs) + 1) s r2 CP ltac:(rewrite V10; f_equal; lia) S22 S2) as (r3 & M3 & RUN3 & K3 & FR3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|]. split; [|exact FR3].
    eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2 | exact K3]. }
Qed.
End FPX_1.
