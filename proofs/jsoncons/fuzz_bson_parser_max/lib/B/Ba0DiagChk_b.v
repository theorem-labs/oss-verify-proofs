(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0DiagStrlen_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r50950_509ec_b Ba0_code_r50c28_50c30_b Ba0_code_r4f2d8_4f480_b Ba0_code_r4de14_4df90_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

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
  Variables p N s : Z.                             (* [comment removed for export] *)
  Hypothesis HN : (0 < N <= 2 ^ 40)%Z.
  Hypothesis Happ : in_app8 p N.
  Hypothesis Hp0 : (0 < p)%Z.
  Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hsh : (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z.                    (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true.
  Hypothesis HG : rt_layout_globs M.
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ret_ok_67130 : ret_ok (0x67548 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma chk1_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p ->
    exists regs',
      msteps ASEGS (mkst regs (0x674b4 : word) M rom) (mkst regs' (0x67414 : word) M rom)
      /\ keeps_but [23]%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H22.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepiv F_6709c D_6709c (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_670a0 D_670a0 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).                   (* [comment removed for export] *)
      stepb_ft F_670a4 D_670a4 ltac:(cond).                                              (* [comment removed for export] *)
      stepiv F_670a8 D_670a8 (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).   (* [comment removed for export] *)
      stepn F_670ac D_670ac.                                                             (* [comment removed for export] *)
      stepb_ft F_670b0 D_670b0 ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_670b4 D_670b4.                                                             (* [comment removed for export] *)
      mld F_670b8 D_670b8 (0x1374c0 : word) G1.                                           (* [comment removed for export] *)
      stepiv F_670bc D_670bc (Z_to_bv 64 (p + N)) ltac:(wval).                            (* [comment removed for export] *)
      mld F_670c0 D_670c0 (0x13fc38 : word) G2.                                           (* [comment removed for export] *)
      stepiv F_670c4 D_670c4 (Z_to_bv 64 (p / 8)) ltac:(wval).                            (* [comment removed for export] *)
      stepiv F_670c8 D_670c8 (Z_to_bv 64 (p + N - 1)) ltac:(wval).                        (* [comment removed for export] *)
      stepiv F_670cc D_670cc (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).                  (* [comment removed for export] *)
      stepiv F_670d0 D_670d0 (Z_to_bv 64 fS) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_670d4 D_670d4 (Z_to_bv 64 lS) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_670d8 D_670d8 (Z_to_bv 64 faS) ltac:(aval).                                (* [comment removed for export] *)
      stepiv F_670dc D_670dc (Z_to_bv 64 laS) ltac:(aval).                                (* [comment removed for export] *)
      mldw F_670e0 D_670e0 faS R0 (repeat (Z_to_bv 8 0 : byte) 8).                        (* [comment removed for export] *)
      mldw F_670e4 D_670e4 laS R1 (repeat (Z_to_bv 8 0 : byte) 8).                        (* [comment removed for export] *)
      stepov F_670e8 D_670e8 (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).                (* [comment removed for export] *)
      stepb_tk F_670ec D_670ec ltac:(cond).                                              (* [comment removed for export] *)
      apply mst_refl.
    - solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition frame72 (M' : word -> option byte) : Prop :=
    (forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M' x = M x) /\ mem_grows M M'.
  Lemma frame72_refl : frame72 M.  Proof. split; [intros x _; reflexivity | apply mem_grows_refl]. Qed.

  Lemma region_call : forall regs (ra : word), (64 < N)%Z -> ret_ok ra ->
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 N -> getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7b4c0 : word) M rom) (mkst regs' ra M' rom)
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
      msteps ASEGS (mkst regs (0x674b4 : word) M rom) (mkst regs' (0x67414 : word) M' rom)
      /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H22 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x674b4 : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x67548 : word) /\ keeps_but [1; 23]%bv regs r1)).
    { eexists. split.
      - stepiv F_6709c D_6709c (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_670a0 D_670a0 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).                   (* [comment removed for export] *)
        stepb_ft F_670a4 D_670a4 ltac:(cond).                                              (* [comment removed for export] *)
        stepiv F_670a8 D_670a8 (Z_to_bv 64 (N - 65)) ltac:(wval).                           (* [comment removed for export] *)
        stepn F_670ac D_670ac.                                                             (* [comment removed for export] *)
        stepb_tk F_670b0 D_670b0 ltac:(cond).                                              (* [comment removed for export] *)
        stepb_tk F_67370 D_67370 ltac:(cond).                                              (* [comment removed for export] *)
        stepiv F_67124 D_67124 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_67128 D_67128 (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
        stepn F_6712c D_6712c.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
    destruct (region_call r1 (0x67548 : word) Hn64 ret_ok_67130 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    eexists. exists M2. split; [|split; [|exact FR2]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepb_tk F_67130 D_67130 ltac:(cond).                                                (* [comment removed for export] *)
      apply mst_refl.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  Theorem chk1_run : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x674b4 : word) M rom) (mkst regs' (0x67414 : word) M' rom)
      /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs H10 H22 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
    - destruct (chk1_fast regs Hle H10 H22) as (r & RUN & K). exists r, M. split; [exact RUN | split; [|exact frame72_refl]].
      intros x Hx Hn. apply K; [exact Hx|]. intros [E|[]]. apply Hn. right. left. exact E.
    - apply chk1_region; [lia | assumption..].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ret_ok_64e00 : ret_ok (0x65218 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma chk2_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps ASEGS (mkst regs (0x65080 : word) M rom) (mkst regs' (0x650e0 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [9; 20]%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H18 H20.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepb_ft F_64c68 D_64c68 ltac:(cond).                                              (* [comment removed for export] *)
      stepb_tk F_64c6c D_64c6c ltac:(cond).                                              (* [comment removed for export] *)
      stepiv F_64d24 D_64d24 (Z_to_bv 64 (N - 1)) ltac:(wval).                            (* [comment removed for export] *)
      stepiv F_64d28 D_64d28 (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_64d2c D_64d2c (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).                   (* [comment removed for export] *)
      stepn F_64d30 D_64d30.                                                             (* [comment removed for export] *)
      stepn F_64d34 D_64d34.                                                             (* [comment removed for export] *)
      stepb_tk F_64d38 D_64d38 ltac:(cond).                                              (* [comment removed for export] *)
      stepiv F_64c80 D_64c80 (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).   (* [comment removed for export] *)
      stepn F_64c84 D_64c84.                                                             (* [comment removed for export] *)
      stepb_ft F_64c88 D_64c88 ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_64c8c D_64c8c.                                                             (* [comment removed for export] *)
      mld F_64c90 D_64c90 (0x1374c0 : word) G1.                                           (* [comment removed for export] *)
      stepiv F_64c94 D_64c94 (Z_to_bv 64 (p + N)) ltac:(wval).                            (* [comment removed for export] *)
      mld F_64c98 D_64c98 (0x13fc38 : word) G2.                                           (* [comment removed for export] *)
      stepiv F_64c9c D_64c9c (Z_to_bv 64 (p / 8)) ltac:(wval).                            (* [comment removed for export] *)
      stepiv F_64ca0 D_64ca0 (Z_to_bv 64 (p + N - 1)) ltac:(wval).                        (* [comment removed for export] *)
      stepiv F_64ca4 D_64ca4 (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).                  (* [comment removed for export] *)
      stepiv F_64ca8 D_64ca8 (Z_to_bv 64 fS) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_64cac D_64cac (Z_to_bv 64 lS) ltac:(wval).                                 (* [comment removed for export] *)
      stepiv F_64cb0 D_64cb0 (Z_to_bv 64 faS) ltac:(aval).                                (* [comment removed for export] *)
      stepiv F_64cb4 D_64cb4 (Z_to_bv 64 laS) ltac:(aval).                                (* [comment removed for export] *)
      mldw F_64cb8 D_64cb8 faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
      mldw F_64cbc D_64cbc laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
      stepov F_64cc0 D_64cc0 (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).                (* [comment removed for export] *)
      stepb_ft F_64cc4 D_64cc4 ltac:(cond).                                              (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  Lemma chk2_region : forall regs, (64 < N)%Z ->
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x65080 : word) M rom) (mkst regs' (0x650e0 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H18 H20 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x65080 : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x65218 : word)
                  /\ getr r1 21 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs r1)).
    { eexists. split.
      - stepb_ft F_64c68 D_64c68 ltac:(cond).
        stepb_tk F_64c6c D_64c6c ltac:(cond).
        stepiv F_64d24 D_64d24 (Z_to_bv 64 (N - 1)) ltac:(wval).
        stepiv F_64d28 D_64d28 (Z_to_bv 64 N) ltac:(wval).
        stepiv F_64d2c D_64d2c (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepn F_64d30 D_64d30.
        stepn F_64d34 D_64d34.
        stepb_tk F_64d38 D_64d38 ltac:(cond).
        stepiv F_64c80 D_64c80 (Z_to_bv 64 (N - 65)) ltac:(wval).                           (* [comment removed for export] *)
        stepn F_64c84 D_64c84.
        stepb_tk F_64c88 D_64c88 ltac:(cond).                                              (* [comment removed for export] *)
        stepb_tk F_64db4 D_64db4 ltac:(cond).                                              (* [comment removed for export] *)
        stepiv F_64df0 D_64df0 (Z_to_bv 64 (p + N - 1)) ltac:(wval).                        (* [comment removed for export] *)
        stepiv F_64df4 D_64df4 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_64df8 D_64df8 (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
        stepn F_64dfc D_64dfc.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & K1).
    destruct (region_call r1 (0x65218 : word) Hn64 ret_ok_64e00 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    assert (S21 : getr r2 21 = Z_to_bv 64 (p + N - 1)) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_64e00 D_64e00 (Z_to_bv 64 0) ltac:(wval).                                    (* [comment removed for export] *)
      stepiv F_64e04 D_64e04 (Z_to_bv 64 (p + N - 1)) ltac:(wval).                          (* [comment removed for export] *)
      stepb_tk F_64e08 D_64e08 ltac:(cond).                                                (* [comment removed for export] *)
      apply mst_refl.
    - gres; rwH; reflexivity.
    - eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
  Qed.

  Theorem chk2_run : forall regs,
    getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x65080 : word) M rom) (mkst regs' (0x650e0 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs H10 H18 H20 H2. destruct (Z_le_gt_dec N 64) as [Hle|Hgt].
    - destruct (chk2_fast regs Hle H10 H18 H20) as (r & RUN & V & K). exists r, M. split; [exact RUN | split; [exact V | split; [|exact frame72_refl]]].
      intros x Hx Hn. apply K; [exact Hx|]. intros [E|[E|[]]]; apply Hn; subst x; cbv; tauto.
    - apply chk2_region; [lia | assumption..].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ret_ok_6348c : ret_ok (0x638a4 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Variable maxlen : Z.
  Hypothesis Hmax : (N < maxlen < 2 ^ 63)%Z.
  Hypothesis HFL : rdn ASEGS M (0x1374b0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d1768)).     (* [comment removed for export] *)
  Hypothesis HRS : rdn ASEGS M (0x1d1863 : word) 1%nat = Some [Z_to_bv 8 1].                                   (* [comment removed for export] *)

  Lemma chk3_head : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen ->
    exists regs',
      msteps ASEGS (mkst regs (0x63734 : word) M rom) (mkst regs' (0x63760 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ getr regs' 9 = Z_to_bv 64 N /\ getr regs' 18 = Z_to_bv 64 p /\ getr regs' 2 = getr regs 2
      /\ keeps_but [9; 20; 21]%bv regs regs'.
  Proof.
    intros regs H10 H9 H18 H19.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    eexists. split.
    - stepb_ft F_6331c D_6331c ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_63320 D_63320.                                                             (* [comment removed for export] *)
      mld F_63324 D_63324 (0x1374b0 : word) HFL.                                          (* [comment removed for export] *)
      mlbu F_63328 D_63328 (0x1d1863 : word) HRS.                                        (* [comment removed for export] *)
      stepb_ft F_6332c D_6332c ltac:(cond).                                              (* [comment removed for export] *)
      stepiv F_63330 D_63330 (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
      stepb_ft F_63334 D_63334 ltac:(cond).                                              (* [comment removed for export] *)
      stepiv F_63338 D_63338 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).                   (* [comment removed for export] *)
      stepn F_6333c D_6333c.                                                             (* [comment removed for export] *)
      stepn F_63340 D_63340.                                                             (* [comment removed for export] *)
      stepb_ft F_63344 D_63344 ltac:(cond).                                              (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
  Qed.

  Lemma chk3_fast : forall regs, (N <= 64)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 N -> getr regs 18 = Z_to_bv 64 p ->
    exists regs',
      msteps ASEGS (mkst regs (0x63760 : word) M rom) (mkst regs' (0x637a8 : word) M rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but []%bv regs regs'.
  Proof.
    intros regs Hn64 H10 H9 H18.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). pose proof fl_facts as (F1 & F3 & F4 & F5).
    destruct HG as (G1 & G2 & _).
    unfold SB, HIGHEND in *.
    pose proof (zero_word faS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R0. pose proof (zero_word laS ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as R1.
    eexists. split.
    - stepiv F_63348 D_63348 (Z_to_bv 64 (2 ^ 64 + N - 65)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; rewrite (zbv_wrap_up (N + - 65)); f_equal; lia).   (* [comment removed for export] *)
      stepn F_6334c D_6334c.                                                             (* [comment removed for export] *)
      stepb_ft F_63350 D_63350 ltac:(cond).                                              (* [comment removed for export] *)
      stepn F_63354 D_63354.                                                             (* [comment removed for export] *)
      mld F_63358 D_63358 (0x1374c0 : word) G1.
      stepiv F_6335c D_6335c (Z_to_bv 64 (p + N)) ltac:(wval).                            (* [comment removed for export] *)
      mld F_63360 D_63360 (0x13fc38 : word) G2.
      stepiv F_63364 D_63364 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_63368 D_63368 (Z_to_bv 64 (p + N - 1)) ltac:(wval).
      stepiv F_6336c D_6336c (Z_to_bv 64 ((p + N - 1) / 8)) ltac:(wval).
      stepiv F_63370 D_63370 (Z_to_bv 64 fS) ltac:(wval).
      stepiv F_63374 D_63374 (Z_to_bv 64 lS) ltac:(wval).
      stepiv F_63378 D_63378 (Z_to_bv 64 faS) ltac:(aval).
      stepiv F_6337c D_6337c (Z_to_bv 64 laS) ltac:(aval).
      mldw F_63380 D_63380 faS R0 (repeat (Z_to_bv 8 0 : byte) 8).
      mldw F_63384 D_63384 laS R1 (repeat (Z_to_bv 8 0 : byte) 8).
      stepov F_63388 D_63388 (Z_to_bv 64 0) ltac:(gres; rwH; reflexivity).
      stepb_ft F_6338c D_6338c ltac:(cond).
      apply mst_refl.
    - split; [gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  Lemma chk3_region : forall regs, (64 < N)%Z ->
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 N -> getr regs 18 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x63760 : word) M rom) (mkst regs' (0x637a8 : word) M' rom)
      /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 18; 22]%bv regs regs' /\ frame72 M'.
  Proof.
    intros regs Hn64 H10 H9 H18 H2.
    pose proof p_facts as (Pp & Ppn & Pp8 & Pq). unfold SB, HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x63760 : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 N /\ getr r1 2 = Z_to_bv 64 s /\ getr r1 1 = (0x638a4 : word)
                  /\ getr r1 22 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 18; 22]%bv regs r1)).
    { eexists. split.
      - stepiv F_63348 D_63348 (Z_to_bv 64 (N - 65)) ltac:(wval).
        stepn F_6334c D_6334c.
        stepb_tk F_63350 D_63350 ltac:(cond).                                              (* [comment removed for export] *)
        stepb_tk F_63440 D_63440 ltac:(cond).                                              (* [comment removed for export] *)
        stepiv F_6347c D_6347c (Z_to_bv 64 (N - 1)) ltac:(wval).                            (* [comment removed for export] *)
        stepiv F_63480 D_63480 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_63484 D_63484 (Z_to_bv 64 N) ltac:(wval).                                  (* [comment removed for export] *)
        stepn F_63488 D_63488.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q22 & K1).
    destruct (region_call r1 (0x638a4 : word) Hn64 ret_ok_6348c Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & K2 & FR2).
    assert (S22 : getr r2 22 = Z_to_bv 64 (N - 1)) by (rewrite (K2 22%bv) by (cbv; tauto); exact Q22).
    eexists. exists M2. split; [|split; [|split; [|exact FR2]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepiv F_6348c D_6348c (Z_to_bv 64 0) ltac:(wval).                                    (* [comment removed for export] *)
      stepiv F_63490 D_63490 (Z_to_bv 64 (N - 1)) ltac:(wval).                              (* [comment removed for export] *)
      stepb_tk F_63494 D_63494 ltac:(cond).                                                (* [comment removed for export] *)
      apply mst_refl.
    - gres; rwH; reflexivity.
    - eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|]. solve_keeps_but.
  Qed.

  Theorem chk3_run : forall regs,
    getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen -> getr regs 2 = Z_to_bv 64 s ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x63734 : word) M rom) (mkst regs' (0x637a8 : word) M' rom)
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

(* [comment removed for export] *)
Definition chk_pre (M : word -> option byte) (p N s : Z) : Prop :=
  (0 < N <= 2 ^ 40)%Z /\ in_app8 p N /\ (0 < p)%Z /\ ((0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z) /\ (SB + (p + N - 1) / 8 + 8 <= s - 72)%Z
  /\ store_ok ASEGS M (Z_to_bv 64 (s - 72)) 72%nat = true /\ rt_layout_globs M
  /\ (forall x : word, (SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + N - 1) / 8 + 8) (SB + 2 ^ 44))%Z -> M x = Some (Z_to_bv 8 0)).

Theorem chk1 : forall M rom p N s regs, chk_pre M p N s ->
  getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x674b4 : word) M rom) (mkst regs' (0x67414 : word) M' rom)
    /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (chk1_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk2 : forall M rom p N s regs, chk_pre M p N s ->
  getr regs 10 = Z_to_bv 64 (p + N - 1) -> getr regs 18 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x65080 : word) M rom) (mkst regs' (0x650e0 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 (p + N - 1) /\ keeps_but [1; 9; 18; 20; 21]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (chk2_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl regs).
Qed.
Theorem chk3 : forall M rom p N s maxlen regs, chk_pre M p N s -> (N < maxlen < 2 ^ 63)%Z ->
  rdn ASEGS M (0x1374b0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d1768)) -> rdn ASEGS M (0x1d1863 : word) 1%nat = Some [Z_to_bv 8 1] ->
  getr regs 10 = Z_to_bv 64 (N - 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 maxlen -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x63734 : word) M rom) (mkst regs' (0x637a8 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 (N - 1) /\ keeps_but [1; 9; 18; 20; 21; 22]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p N s maxlen regs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) B1 B2 B3.
  exact (chk3_run M rom p N s A1 A2 A3 A4 A5 A6 A7 A8 _ _ _ _ eq_refl eq_refl eq_refl eq_refl maxlen B1 B2 B3 regs).
Qed.

(* [comment removed for export] *)
Lemma ret_ok_6709c : ret_ok (0x674b4 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Theorem strlen_chk1 : forall M rom p s (bs : list byte) regs,
  rdn ASEGS M (Z_to_bv 64 p) (length bs + 1) = Some (bs ++ [Z_to_bv 8 0]) ->
  (forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) <> 0%Z) ->
  chk_pre M p (Z.of_nat (length bs) + 1) s ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 22 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 s ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x674b0 : word) M rom) (mkst regs' (0x67414 : word) M' rom)
    /\ keeps_but [1; 23]%bv regs regs' /\ frame72 M s M'.
Proof.
  intros M rom p s bs regs HS HNZ CP H10 H22 H2.
  assert (Hp : (0 <= p)%Z /\ (p + Z.of_nat (length bs) + 1 < 2 ^ 63)%Z).
  { destruct CP as (_ & A2 & _). unfold in_app8, LOWEND, HIGHBEG, HIGHEND in A2. lia. }
  assert (S1 : exists r1, msteps ASEGS (mkst regs (0x674b0 : word) M rom) (mkst r1 (0x8b5b4 : word) M rom)
            /\ (getr r1 1 = (0x674b4 : word) /\ getr r1 10 = Z_to_bv 64 p /\ getr r1 22 = Z_to_bv 64 p /\ getr r1 2 = Z_to_bv 64 s /\ keeps_but [1; 23]%bv regs r1)).
  { eexists. split.
    + stepn F_67098 D_67098. apply mst_refl.
    + repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
  destruct S1 as (r1 & RUN1 & R1 & R10 & R22 & R2 & K1).
  { 
    destruct (internal_strlen_run M rom p bs Hp HS HNZ r1 (0x674b4 : word) ret_ok_6709c R1 R10) as (r2 & RUN2 & V10 & K2).
    assert (S22 : getr r2 22 = Z_to_bv 64 p) by (rewrite (K2 22%bv) by (cbv; tauto); exact R22).
    assert (S2 : getr r2 2 = Z_to_bv 64 s) by (rewrite (K2 2%bv) by (cbv; tauto); exact R2).
    destruct (chk1 M rom p (Z.of_nat (length bs) + 1) s r2 CP ltac:(rewrite V10; f_equal; lia) S22 S2) as (r3 & M3 & RUN3 & K3 & FR3).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|]. split; [|exact FR3].
    eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2 | exact K3]. }
Qed.
End FPX_1.
