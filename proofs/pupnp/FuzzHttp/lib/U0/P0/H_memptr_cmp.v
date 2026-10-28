(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_strncmp F_strlen F_ctype HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition memptr_cmp_entry := 0x16570%Z.
Definition memptr_cmp_nocase_entry := 0x16600%Z.
Definition strncasecmp_entry := 0x2493c%Z.

Ltac sstep := step; fix_lit_store.

Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma strncmp_walk_some : forall str l slack k,
  (length l > k)%nat ->
  exists v, strncmp_walk l (str ++ Z_to_bv 8 0 :: slack) k = Some v /\ (-255 <= v <= 255)%Z.
Proof.
  induction str as [|c str IH]; intros l slack k Hl.
  - destruct l as [|a l']; [cbn in Hl; lia|]. cbn [app strncmp_walk].
    pose proof (byte_range a). replace (bv_unsigned (Z_to_bv 8 0)) with 0%Z by reflexivity.
    rewrite (proj2 (Z.eqb_eq 0 0) eq_refl). rewrite orb_true_r. cbn [orb]. eexists; split; [reflexivity|lia].
  - destruct l as [|a l']; [cbn in Hl; lia|]. cbn [app strncmp_walk].
    pose proof (byte_range a). pose proof (byte_range c).
    destruct (_ || _ || _ || _)%bool eqn:E; [eexists; split; [reflexivity|lia]|].
    destruct k as [|k'].
    { exfalso. revert E. cbn [Nat.eqb]. rewrite orb_true_r. cbn [orb]. discriminate. }
    apply IH. cbn in Hl. lia.
Qed.

Lemma strncmp_model_some : forall str l slack n,
  (0 <= n)%Z -> (Z.of_nat (length l) >= n)%Z ->
  exists v, strncmp_model l (str ++ Z_to_bv 8 0 :: slack) n = Some v /\ (-255 <= v <= 255)%Z.
Proof.
  intros str l slack n Hn Hl. unfold strncmp_model. destruct (Z.eqb_spec n 0).
  - eexists; split; [reflexivity|lia].
  - apply strncmp_walk_some. lia.
Qed.

Definition memptr_cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 32) (bv_unsigned sp)
    /\ (-255 <= r <= 255)%Z.

Definition memptr_cmp_stmt_at (entry : Z) : Prop :=
  forall (MP T n S : Z) (tok str slack : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m MP (memptr_cells T n) ->
  bytes_at rsegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n < 2^63)%Z ->
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->

  (MP + 16 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= MP)%Z ->
  (T + Z.of_nat (length tok) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= T)%Z ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= S)%Z ->
  (0 < MP)%Z -> (MP mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz MP -> a1 = wz S ->
  evt rsegs (memptr_cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz entry) fc None m (seg_rom rsegs)).

Definition memptr_cmp_stmt : Prop := memptr_cmp_stmt_at memptr_cmp_entry.

Lemma memptr_cmp_spec : memptr_cmp_stmt.
Proof.
  unfold memptr_cmp_stmt, memptr_cmp_stmt_at, memptr_cmp_entry.
  intros until m. intros MPC TOK TL N0 STR NONUL PAD ST SPLO SEP1 SEP2 SEP3 MPNZ MPAL MI -> ->.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ MPC) as B1. cbn [cells_size csize Nat.add memptr_cells] in B1.
  pose proof (bytes_at_bound _ _ _ _ TOK) as B2. pose proof (bytes_at_bound _ _ _ _ STR) as B3.
  rewrite length_app in B3. cbn [length] in B3.
  unfold memptr_cells in MPC.
  carve_frame 32%nat ST.
  sstep. sstep. sstep. sstep. sstep. ub_null. zstep. ub_align. sstep. sstep. sstep. sstep. sstep. sstep.

  destruct (strncmp_model_some str tok slack n ltac:(lia) TL) as (v & HM & HV).
  call strncmp_spec.
  all: try (rewrite ?unsigned_lit by lia; first [exact TOK | exact STR | exact HM | exact MI]).
  all: try (rewrite ?unsigned_lit by lia; first [exact TOK | exact STR | exact HM | exact MI]).
  step. if_cases K; zify_cond K.
  -
    sstep. sstep. sstep.
    call strlen_spec.
    all: try (rewrite ?unsigned_lit by lia; first [exact STR | exact NONUL | exact PAD | assumption]).
    step. step. step. if_cases K2; zify_cond K2.
    + sstep. sstep. sstep. sstep. sstep. sstep. release_frame FR ST (bv_unsigned sp). finish; lia.
    + sstep. sstep. sstep. sstep. sstep. sstep. sstep. release_frame FR ST (bv_unsigned sp). finish; lia.
  - sstep. sstep. sstep. sstep. sstep. sstep. release_frame FR ST (bv_unsigned sp). finish; lia.
Qed.

Definition strncasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 48) (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

Definition strncasecmp_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ls rs : list byte) (v : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  strncasecmp_model ls rs (bv_unsigned a2) = Some v ->
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) -> (64 <= bv_unsigned sp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strncasecmp_entry) fc None m (seg_rom rsegs)).

Lemma to_lower_range_b : forall b : byte, (0 <= to_lower (bv_unsigned b) < 256)%Z.
Proof. intros b. apply to_lower_range. apply byte_range. Qed.

Lemma strncasecmp_walk_some : forall str l slack k,
  (length l > k)%nat ->
  exists v, strncasecmp_walk l (str ++ Z_to_bv 8 0 :: slack) k = Some v /\ (-255 <= v <= 255)%Z.
Proof.
  induction str as [|c str IH]; intros l slack k Hl.
  - destruct l as [|a l']; [cbn in Hl; lia|]. cbn [app strncasecmp_walk].
    pose proof (to_lower_range_b a). replace (bv_unsigned (Z_to_bv 8 0)) with 0%Z by reflexivity.
    rewrite (proj2 (Z.eqb_eq 0 0) eq_refl). rewrite orb_true_r. cbn [orb]. change (to_lower 0) with 0%Z.
    eexists; split; [reflexivity|lia].
  - destruct l as [|a l']; [cbn in Hl; lia|]. cbn [app strncasecmp_walk].
    pose proof (to_lower_range_b a). pose proof (to_lower_range_b c).
    destruct (_ || _ || _ || _)%bool eqn:E; [eexists; split; [reflexivity|lia]|].
    destruct k as [|k'].
    { exfalso. revert E. cbn [Nat.eqb]. rewrite orb_true_r. cbn [orb]. discriminate. }
    apply IH. cbn in Hl. lia.
Qed.

Lemma strncasecmp_model_some : forall str l slack n,
  (0 <= n)%Z -> (Z.of_nat (length l) >= n)%Z ->
  exists v, strncasecmp_model l (str ++ Z_to_bv 8 0 :: slack) n = Some v /\ (-255 <= v <= 255)%Z.
Proof.
  intros str l slack n Hn Hl. unfold strncasecmp_model. destruct (Z.eqb_spec n 0).
  - eexists; split; [reflexivity|lia].
  - apply strncasecmp_walk_some. lia.
Qed.

Definition memptr_cmp_nocase_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 80) (bv_unsigned sp)
    /\ (-255 <= r <= 255)%Z.

Definition memptr_cmp_nocase_stmt : Prop :=
  forall (MP T n S : Z) (tok str slack : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m MP (memptr_cells T n) ->
  bytes_at rsegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n < 2^63)%Z ->
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m (bv_unsigned sp - 80) (bv_unsigned sp) -> (128 <= bv_unsigned sp)%Z ->
  (MP + 16 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= MP)%Z ->
  (T + Z.of_nat (length tok) <= bv_unsigned sp - 80 \/ bv_unsigned sp <= T)%Z ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 80 \/ bv_unsigned sp <= S)%Z ->
  (0 < MP)%Z -> (MP mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz MP -> a1 = wz S ->
  evt rsegs (memptr_cmp_nocase_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz memptr_cmp_nocase_entry) fc None m (seg_rom rsegs)).

Definition memptr_cmp_qpost (d : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(q - d, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (q - d) q
    /\ (-255 <= r <= 255)%Z.

Definition memptr_cmp_qstmt (d entry : Z) : Prop :=
  forall (MP T n S : Z) (tok str slack : list byte) (q : Z)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m MP (memptr_cells T n) ->
  bytes_at rsegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n < 2^63)%Z ->
  bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m (q - d) q -> (128 <= q < 2^64)%Z ->
  (MP + 16 <= q - d \/ q <= MP)%Z ->
  (T + Z.of_nat (length tok) <= q - d \/ q <= T)%Z ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= q - d \/ q <= S)%Z ->
  (0 < MP)%Z -> (MP mod 8 = 0)%Z -> mem_inv rsegs m -> a0 = wz MP -> a1 = wz S ->
  evt rsegs (memptr_cmp_qpost d ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz entry) fc None m (seg_rom rsegs)).

Lemma memptr_cmp_call : memptr_cmp_qstmt 32 memptr_cmp_entry.
Proof.
  unfold memptr_cmp_qstmt. intros until m. intros MPC TOK TL N0 STR NONUL PAD ST Hq SEP1 SEP2 SEP3 MPNZ MPAL MI Ha0 Ha1.
  assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memptr_cmp_spec MP T n S tok str slack); rewrite ?E; eauto; lia. }
  intros ms' P. unfold memptr_cmp_post in P. rewrite !E in P. exact P.
Qed.

Section NOCASE.
Context {HCEIL : HasCeiling}.
  Hypothesis strncasecmp_spec : strncasecmp_stmt.

  Definition strncasecmp_qpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0 a1 : word) (ls rs : list byte) (v : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(q - 48, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' (q - 48) q
      /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

  #[using="strncasecmp_spec"] Lemma strncasecmp_call : forall (q : Z) ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (ls rs : list byte) (v : Z),
    bytes_at rsegs m (bv_unsigned a0) ls ->
    bytes_at rsegs m (bv_unsigned a1) rs ->
    strncasecmp_model ls rs (bv_unsigned a2) = Some v ->
    stk rsegs m (q - 48) q -> (64 <= q < 2^64)%Z ->
    (bv_unsigned a0 + Z.of_nat (length ls) <= q - 48 \/ q <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + Z.of_nat (length rs) <= q - 48 \/ q <= bv_unsigned a1)%Z ->
    mem_inv rsegs m ->
    evt rsegs (strncasecmp_qpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 strncasecmp_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until v. intros LS RS HM ST Hq S1 S2 MI.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    unfold strncasecmp_stmt in strncasecmp_spec.
    eapply evt_mono. { eapply strncasecmp_spec; rewrite ?E; eauto; lia. }
    intros ms' P. unfold strncasecmp_post in P. rewrite !E in P. exact P.
  Qed.

  #[using="strncasecmp_spec"] Lemma memptr_cmp_nocase_spec : memptr_cmp_nocase_stmt.
  Proof.
    unfold memptr_cmp_nocase_stmt, memptr_cmp_nocase_entry.
    intros until m. intros MPC TOK TL N0 STR NONUL PAD ST SPLO SEP1 SEP2 SEP3 MPNZ MPAL MI -> ->.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (rw_cells_bound rsegs _ _ _ MPC) as B1. cbn [cells_size csize Nat.add memptr_cells] in B1.
    pose proof (bytes_at_bound _ _ _ _ TOK) as B2. pose proof (bytes_at_bound _ _ _ _ STR) as B3.
    rewrite length_app in B3. cbn [length] in B3.
    unfold memptr_cells in MPC.
    carve_frame 32%nat ST.
    sstep. sstep. sstep. sstep. sstep. ub_null. zstep. ub_align. sstep. sstep. sstep. sstep. sstep. sstep.
    destruct (strncasecmp_model_some str tok slack n ltac:(lia) TL) as (v & HM & HV).
    pose proof (word_lt64 sp) as SPR.
    replace (bv_unsigned sp - 80)%Z with (bv_unsigned sp + -32 - 48)%Z in ST by lia.
    call strncasecmp_call.
    all: side (rewrite ?unsigned_lit by lia; rewrite ?length_app; cbn [length];
               first [exact TOK | exact STR | exact HM | exact MI | exact ST | lia]).
    all: side (rewrite ?unsigned_lit by lia; rewrite ?length_app; cbn [length];
               first [exact TOK | exact STR | exact HM | exact MI | exact ST | lia]).
    rename PC into ST. rewrite unsigned_lit in PC0, POST by lia.
    step. if_cases K; zify_cond K.
    - sstep. sstep. sstep.
      call strlen_spec.
      all: side (rewrite ?unsigned_lit by lia; first [exact POST | exact NONUL | exact PAD | assumption]).
      step. step. step. if_cases K2; zify_cond K2.
      + sstep. sstep. sstep. sstep. sstep. sstep.
        replace (bv_unsigned sp + -32 - 48)%Z with (bv_unsigned sp - 80)%Z in ST by lia.
        release_frame FR ST (bv_unsigned sp). finish; lia.
      + sstep. sstep. sstep. sstep. sstep. sstep. sstep.
        replace (bv_unsigned sp + -32 - 48)%Z with (bv_unsigned sp - 80)%Z in ST by lia.
        release_frame FR ST (bv_unsigned sp). finish; lia.
    - sstep. sstep. sstep. sstep. sstep. sstep.
      replace (bv_unsigned sp + -32 - 48)%Z with (bv_unsigned sp - 80)%Z in ST by lia.
      release_frame FR ST (bv_unsigned sp). finish; lia.
  Qed.

  #[using="strncasecmp_spec"] Lemma memptr_cmp_nocase_call : memptr_cmp_qstmt 80 memptr_cmp_nocase_entry.
  Proof.
    unfold memptr_cmp_qstmt. intros until m. intros MPC TOK TL N0 STR NONUL PAD ST Hq SEP1 SEP2 SEP3 MPNZ MPAL MI Ha0 Ha1.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    eapply evt_mono.
    { eapply (memptr_cmp_nocase_spec MP T n S tok str slack); rewrite ?E; eauto; lia. }
    intros ms' P. unfold memptr_cmp_nocase_post in P. rewrite !E in P. exact P.
  Qed.
End NOCASE.
