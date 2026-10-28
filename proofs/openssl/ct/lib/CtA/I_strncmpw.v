(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit I_pck D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISTRNCMP_DEPTH := 2256%Z (only parsing).

(* [comment removed for export] *)
Definition icells_sc (m : mem) : Prop :=
  ro_cells ctasegs m 0x5a9228 [C8 (Z_to_bv 64 0x703b68)]           (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x5a9238 [C8 (Z_to_bv 64 0x672038)]         (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x672038 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ rw_cells ctasegs m 0x672d18 [C1 (Z_to_bv 8 1)]                (* [comment removed for export] *)
  /\ ro_cells ctasegs m 0x703c5d [C1 (Z_to_bv 8 0)].             (* [comment removed for export] *)

Lemma icells_sc_agree : forall m m', icells_sc m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono ctasegs m m' -> icells_sc m'.
Proof.
  intros m m' (C1 & C2 & C3 & C4 & C5) AG WM.
  split; [| split; [| split; [| split]]].
  - apply (ro_cells_agree ctasegs m m' _ _ C1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree ctasegs m m' _ _ C2). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree ctasegs m m' _ _ C3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree ctasegs m m' _ _ C4); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (ro_cells_agree ctasegs m m' _ _ C5). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

Lemma m2s_cells_agree : forall m m', m2s_cells m -> agree_on (fun x => 0 <= x < 0x1000000) m m' -> wmono ctasegs m m' -> m2s_cells m'.
Proof.
  intros m m' (C1 & C2 & C3) AG WM.
  split; [| split].
  - apply (rw_cells_agree ctasegs m m' _ _ C1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree ctasegs m m' _ _ C2); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
  - apply (rw_cells_agree ctasegs m m' _ _ C3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cmpx (x1 x2 : Z) : Z := if x1 <? x2 then -1 else if x2 <? x1 then 1 else 0.

Definition sc_pre (b1 b2 : list byte) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists z, nth_error b1 j = Some z /\ nth_error b2 j = Some z /\ bv_unsigned z <> 0.

Lemma sc_pre_S : forall b1 b2 k x, sc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some x -> bv_unsigned x <> 0 ->
  sc_pre b1 b2 (S k).
Proof.
  intros b1 b2 k x HP H1 H2 HX j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [exists x; auto|]. apply HP. lia.
Qed.

Lemma sc_pre_tl : forall x1 x2 b1 b2 k, sc_pre (x1 :: b1) (x2 :: b2) (S k) -> sc_pre b1 b2 k.
Proof. intros x1 x2 b1 b2 k HP j Hj. destruct (HP (S j) ltac:(lia)) as (z & E1 & E2 & NZ). exists z. cbn in E1, E2. auto. Qed.

Lemma idx_aux_step : forall z b1 b2 K, bv_unsigned z <> 0 ->
  strncmp_idx_aux (z :: b1) (z :: b2) (S K) = S (strncmp_idx_aux b1 b2 K).
Proof.
  intros z b1 b2 K NZ. cbn [strncmp_idx_aux]. rewrite Z.eqb_refl. cbn [negb orb].
  rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
Qed.

Lemma idx_aux_break : forall k K b1 b2 x y,
  (k < K)%nat -> sc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  strncmp_idx_aux b1 b2 K = k.
Proof.
  induction k as [|k IH]; intros K b1 b2 x y HK HP H1 H2 HB.
  - destruct K as [|K']; [lia|]. destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in H1, H2. injection H1 as ->. injection H2 as ->. cbn [strncmp_idx_aux].
    destruct HB as [HB|HB].
    + rewrite (proj2 (Z.eqb_neq _ _) HB). reflexivity.
    + rewrite HB. cbn. rewrite orb_true_r. reflexivity.
  - destruct K as [|K']; [lia|].
    destruct (HP 0%nat ltac:(lia)) as (z & Hz1 & Hz2 & Hnz).
    destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
    rewrite idx_aux_step by exact Hnz. f_equal.
    apply (IH K' b1' b2' x y); [lia| exact (sc_pre_tl _ _ _ _ _ HP)| exact H1| exact H2| exact HB].
Qed.

Lemma idx_aux_full : forall K b1 b2, sc_pre b1 b2 K -> strncmp_idx_aux b1 b2 K = K.
Proof.
  induction K as [|K IH]; intros b1 b2 HP; [destruct b1; reflexivity|].
  destruct (HP 0%nat ltac:(lia)) as (z & Hz1 & Hz2 & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite idx_aux_step by exact Hnz. f_equal. apply IH. exact (sc_pre_tl _ _ _ _ _ HP).
Qed.

Lemma idx_aux_ge : forall k K b1 b2, (k <= K)%nat -> sc_pre b1 b2 k -> (k <= strncmp_idx_aux b1 b2 K)%nat.
Proof.
  induction k as [|k IH]; intros K b1 b2 HK HP; [lia|].
  destruct K as [|K']; [lia|].
  destruct (HP 0%nat ltac:(lia)) as (z & Hz1 & Hz2 & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite idx_aux_step by exact Hnz. specialize (IH K' b1' b2' ltac:(lia) (sc_pre_tl _ _ _ _ _ HP)). lia.
Qed.

Lemma idx_aux_le : forall K b1 b2, (strncmp_idx_aux b1 b2 K <= K)%nat.
Proof.
  induction K as [|K IH]; intros b1 b2; [destruct b1; cbn; lia|].
  destruct b1 as [|x1 b1']; [cbn; lia|]. destruct b2 as [|y1 b2']; [cbn; lia|].
  cbn [strncmp_idx_aux]. destruct (_ || _); [lia|]. specialize (IH b1' b2'). lia.
Qed.

(* [comment removed for export] *)
Lemma res_break : forall n b1 b2 k x y, 0 <= n -> (k < Z.to_nat n)%nat -> sc_pre b1 b2 k ->
  nth_error b1 k = Some x -> nth_error b2 k = Some y -> (bv_unsigned x <> bv_unsigned y \/ bv_unsigned x = 0) ->
  strncmp_idx n b1 b2 = Z.of_nat k /\ strncmp_res n b1 b2 = cmpx (bv_unsigned x) (bv_unsigned y).
Proof.
  intros n b1 b2 k x y N0 HK HP H1 H2 HB.
  assert (E : strncmp_idx n b1 b2 = Z.of_nat k) by (unfold strncmp_idx; rewrite (idx_aux_break k _ b1 b2 x y HK HP H1 H2 HB); reflexivity).
  split; [exact E|]. unfold strncmp_res. rewrite E. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite Nat2Z.id, H1, H2. reflexivity.
Qed.

Lemma res_full : forall n b1 b2, 0 <= n -> sc_pre b1 b2 (Z.to_nat n) ->
  strncmp_idx n b1 b2 = n /\ strncmp_res n b1 b2 = 0.
Proof.
  intros n b1 b2 N0 HP.
  assert (E : strncmp_idx n b1 b2 = n) by (unfold strncmp_idx; rewrite (idx_aux_full _ b1 b2 HP); lia).
  split; [exact E|]. unfold strncmp_res. rewrite E, Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma idx_aux_firstn : forall K b1 b2 j, (strncmp_idx_aux b1 b2 K < j \/ K <= j)%nat ->
  strncmp_idx_aux (firstn j b1) (firstn j b2) K = strncmp_idx_aux b1 b2 K.
Proof.
  induction K as [|K IH]; intros b1 b2 j HJ; [destruct b1, j; reflexivity|].
  destruct j as [|j']; [cbn in HJ; lia|].
  destruct b1 as [|x1 b1']; [reflexivity|]. destruct b2 as [|y1 b2']; [rewrite firstn_nil; reflexivity|].
  cbn [firstn strncmp_idx_aux]. cbn [strncmp_idx_aux] in HJ.
  destruct (_ || _); [reflexivity|]. f_equal. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma isc_cmp_loop : forall (r k : nat) (n p1 p2 : Z) (b1 b2 : list byte)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  n = Z.of_nat (k + S r) -> n < 2^31 ->
  bytes_at ctasegs m p1 b1 -> bytes_at ctasegs m p2 b2 -> strncmp_ok n b1 b2 -> sc_pre b1 b2 k -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a0' : word) (x1 x2 : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4 s5 s6 s7 (Z_to_bv 64 x1) (Z_to_bv 64 x2) s10
                    (Z_to_bv 64 (strncmp_idx n b1 b2)) t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ae208) fc None m (seg_rom ctasegs)
      /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ cmpx x1 x2 = strncmp_res n b1 b2)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (Z.of_nat k)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae1e0) fc None m (seg_rom ctasegs)).
Proof.
  induction r as [|r IH]; intros k n p1 p2 b1 b2 ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m
    Hn HN B1 B2 OK HP MI;
  ( pose proof (idx_aux_ge k (Z.to_nat n) b1 b2 ltac:(lia) HP) as GE;
    pose proof OK as (L1 & L2); unfold strncmp_sz, strncmp_idx in L1, L2;
    destruct (nth_error b1 k) as [x|] eqn:E1; [| apply nth_error_None in E1; lia];
    destruct (nth_error b2 k) as [y|] eqn:E2; [| apply nth_error_None in E2; lia];
    pose proof (bytes_at_nth1 ctasegs m p1 b1 k x B1 E1) as BX; pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_nth1 ctasegs m p2 b2 k y B2 E2) as BY; pose proof (ro_C1_of_bytes m _ _ BY) as CY;
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1; pose proof (bytes_at_bound _ _ _ _ B2) as BB2;
    pose proof (bv_unsigned_in_range 8 x) as XR; pose proof (bv_unsigned_in_range 8 y) as YR; unfold bv_modulus in XR, YR;
    change (2 ^ Z.of_N 8) with 256 in XR, YR;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl ctasegs m) as WM;
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia);
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia);
    assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia);
    assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia);
    assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia);
    assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia);
    assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia);
    lstep; set (q1 := p1 + Z.of_nat k) in *; lstep;
    lstep; set (q2 := p2 + Z.of_nat k) in *; lstep;
    cbv beta in *;
    lstep; if_cases K; zify_cond K; rewrite ?EUx, ?EUy in K; change (bv_unsigned z64) with 0 in K).
  - (* [comment removed for export] *)
    destruct (res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
    apply evt_done. eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
    split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - lstep. if_cases K2; zify_cond K2; rewrite ?EUx, ?EUy in K2.
    + destruct (res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
      apply evt_done. eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + assert (Exy : x = y) by (apply bv_eq; exact K2). subst y.
      pose proof (sc_pre_S b1 b2 k x HP E1 E2 K) as HP1.
      lstep. lstep. if_false. lstep. lstep.
      destruct (res_full n b1 b2 ltac:(lia) ltac:(replace (Z.to_nat n) with (S k) by lia; exact HP1)) as (RI & RR).
      apply evt_done. eexists. exists (bv_unsigned x), (bv_unsigned x). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia|]]. rewrite RR. unfold cmpx. rewrite Z.ltb_irrefl. reflexivity.
  - (* [comment removed for export] *)
    destruct (res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
    apply evt_done. eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
    split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - lstep. if_cases K2; zify_cond K2; rewrite ?EUx, ?EUy in K2.
    + destruct (res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
      apply evt_done. eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + assert (Exy : x = y) by (apply bv_eq; exact K2). subst y.
      pose proof (sc_pre_S b1 b2 k x HP E1 E2 K) as HP1.
      lstep. lstep. if_true.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      apply (IH (S k) n p1 p2 b1 b2); [lia| lia| exact B1| exact B2| exact OK| exact HP1| exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma isc_loop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at ctasegs m x [b]) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ae574) fc None m (seg_rom ctasegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae564) fc None m (seg_rom ctasegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

(* [comment removed for export] *)
Lemma isc_rip1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2176) -> lo <= sp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc ctasegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae370) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae57c) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk ctasegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

(* [comment removed for export] *)
Lemma isc_chk1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk ctasegs m lo (sp + -2176) -> lo <= sp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  chk_ok m p n -> m2s_cells m -> icells_sc m -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1ae370) fc None m' (seg_rom ctasegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ae328) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH P0 N0 PN (AC & QW & RO) M2S (G70 & G2 & SHC & AI & SSC) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL].
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (isc_rip1 sp p n); try assumption; lia.
  - (* [comment removed for export] *)
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + n + -1) with (p + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + (* [comment removed for export] *)
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) P0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * (* [comment removed for export] *)
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isc_rip1 sp p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isc_loop1 (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isc_rip1 sp p n); try assumption; lia.
    + apply evt_done. do 17 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End WithRIP.
