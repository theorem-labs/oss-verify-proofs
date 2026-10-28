(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small I_consts I_qck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition imm_entry : Z := 0x920d0.

Definition imm_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(d, d + Z.of_nat (length bs))] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ bytes_at bsegs m' d bs.

Lemma bytes_at_nth : forall (m : mem) a (bs : list byte) j, bytes_at bsegs m a bs -> 0 <= j < Z.of_nat (length bs) ->
  bytes_at bsegs m (a + j) [nth (Z.to_nat j) bs (Z_to_bv 8 0)].
Proof.
  intros m a bs j (H0 & H1 & H) Hj. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
  specialize (H (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H. apply nth_error_nth'. lia.
Qed.

Lemma bytes_at_of_nth : forall (m : mem) a (bs : list byte), 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> bytes_at bsegs m (a + j) [nth (Z.to_nat j) bs (Z_to_bv 8 0)]) -> bytes_at bsegs m a bs.
Proof.
  intros m a bs H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & X). specialize (X 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in X.
  rewrite Z.add_0_r, Nat2Z.id in X. rewrite X. symmetry. apply nth_error_nth'. exact Hi.
Qed.

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : mem) (d s : Z) (bs : list byte).
Notation n := (Z.of_nat (length bs)).
Notation B j := (nth (Z.to_nat j) bs (Z_to_bv 8 0)).
Hypothesis D0 : 0 <= d.
Hypothesis S0 : 0 <= s.
Hypothesis DH : d + n < 2 ^ 63.
Hypothesis SH : s + n < 2 ^ 63.
Notation POST := (imm_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d bs m).

Definition INV (lo hi slo shi : Z) (mi : mem) : Prop :=
  (forall j, lo <= j < hi -> bytes_at bsegs mi (d + j) [B j]) /\ (forall j, slo <= j < shi -> bytes_at bsegs mi (s + j) [B j])
  /\ wr_at bsegs mi d n /\ munch [(d, d + n)] m mi /\ wmono bsegs m mi /\ mem_inv bsegs mi.

Lemma inv_store : forall lo hi slo shi lo' hi' slo' shi' (mi : mem) i,
  INV lo hi slo shi mi -> 0 <= i < n -> slo <= i < shi ->
  (forall j, lo' <= j < hi' -> lo <= j < hi \/ j = i) ->
  (forall j, slo' <= j < shi' -> slo <= j < shi /\ s + j <> d + i) ->
  INV lo' hi' slo' shi' (write_to_mem mi (wa (d + i)) [B i]).
Proof using D0 S0 DH SH.
  intros lo hi slo shi lo' hi' slo' shi' mi i (I1 & I2 & WR & MU & WM & MI) Hi Hsi HD HS.
  assert (SOK : store_ok bsegs mi (wa (d + i)) 1 = true) by (apply (wr_at_store_ok bsegs mi d n i 1 WR); cbn; lia).
  split; [|split; [|split; [|split; [|split]]]].
  - intros j Hj. destruct (HD j Hj) as [X| ->].
    + destruct (Z.eq_dec j i) as [->|NE]; [apply bytes_at_write_same; cbn [length]; lia|].
      apply bytes_at_write_other; [exact (I1 j X) | lia | cbn [length]; lia | cbn [length]; lia].
    + apply bytes_at_write_same; cbn [length]; lia.
  - intros j Hj. destruct (HS j Hj) as (X & NE). apply bytes_at_write_other; [exact (I2 j X) | lia | cbn [length]; lia | cbn [length]; lia].
  - apply wr_at_write. exact WR.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; left; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact SOK].
Qed.
Notation ST pc mi x11 x12 x13 x14 x15 x16 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mi (seg_rom bsegs)).

Lemma imm_done : forall (mi : mem) slo shi x11 x12 x13 x14 x15 x16, INV 0 n slo shi mi -> evt bsegs POST (ST 0x92124 mi x11 x12 x13 x14 x15 x16).
Proof using D0 S0 DH SH.
  intros mi slo shi x11 x12 x13 x14 x15 x16 (I1 & _ & _ & MU & WM & MI).
  zstep.
  apply evt_done. unfold imm_post. do 6 eexists. exists mi. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  apply bytes_at_of_nth; [lia | lia | exact I1].
Qed.

Lemma imm_fwd : forall (k : nat) (i : Z) (mi : mem) x14 x15 x16,
  Z.of_nat (S k) = n - i -> 0 <= i -> d < s -> INV 0 i i n mi ->
  evt bsegs POST (ST 0x920e0 mi (Z_to_bv 64 (s + i)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (d + i)) x14 x15 x16).
Proof using D0 S0 DH SH.
  induction k as [|k IH]; intros i mi x14 x15 x16 Hk Hi Hds I.
  - pose proof I as (I1 & I2 & WR & MU & WM & MI).
    pose proof (ro_C1_of_bytes mi (s + i) _ (I2 i ltac:(lia))) as CB0.
    assert (SOK : store_ok bsegs mi (wa (d + i)) 1 = true) by (apply (wr_at_store_ok bsegs mi d n i 1 WR); cbn; lia).
    assert (EU1 : bv_unsigned (Z_to_bv 64 (s + i)) = s + i) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (d + i)) = d + i) by (apply unsigned_lit; lia).
    set (cs := s + i) in *. set (cd := d + i) in *.
    zstep. zstep.
    change (Z_to_bv 64 (bv_unsigned (B i))) with (zxb (B i)). rewrite le1_zxb. change (Z_to_bv 64 cd) with (wa cd).
    pose proof (inv_store 0 i i n 0 n n n mi i I ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) ltac:(intros j Hj; lia)) as I'.
    fold cd in I'.
    zstep. zstep. zstep.
    replace (cd + 1) with (d + n) by (unfold cd; lia). rewrite bv_eqb_refl. cbv [negb].
    zstep.
    exact (imm_done _ _ _ _ _ _ _ _ _ I').
  - pose proof I as (I1 & I2 & WR & MU & WM & MI).
    pose proof (ro_C1_of_bytes mi (s + i) _ (I2 i ltac:(lia))) as CB0.
    assert (SOK : store_ok bsegs mi (wa (d + i)) 1 = true) by (apply (wr_at_store_ok bsegs mi d n i 1 WR); cbn; lia).
    assert (EU1 : bv_unsigned (Z_to_bv 64 (s + i)) = s + i) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (d + i)) = d + i) by (apply unsigned_lit; lia).
    set (cs := s + i) in *. set (cd := d + i) in *.
    zstep. zstep.
    change (Z_to_bv 64 (bv_unsigned (B i))) with (zxb (B i)). rewrite le1_zxb. change (Z_to_bv 64 cd) with (wa cd).
    pose proof (inv_store 0 i i n 0 (i + 1) (i + 1) n mi i I ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) ltac:(intros j Hj; lia)) as I'.
    fold cd in I'.
    zstep. zstep. zstep.
    subst cs cd.
    assert (EU3 : bv_unsigned (Z_to_bv 64 (d + i + 1)) = d + i + 1) by (apply unsigned_lit; lia).
    assert (EU4 : bv_unsigned (Z_to_bv 64 (d + n)) = d + n) by (apply unsigned_lit; lia).
    if_true.
    replace (s + i + 1) with (s + (i + 1)) by lia. replace (d + i + 1) with (d + (i + 1)) by lia.
    apply (IH (i + 1)); [lia | lia | exact Hds | exact I'].
Qed.

Lemma imm_bwd : forall (k : nat) (i : Z) (mi : mem) x14 x15 x16,
  Z.of_nat k = i -> i < n -> s < d -> INV (i + 1) n 0 (i + 1) mi ->
  evt bsegs POST (ST 0x92108 mi (Z_to_bv 64 s) (Z_to_bv 64 1) (Z_to_bv 64 i) x14 x15 x16).
Proof using D0 S0 DH SH.
  induction k as [|k IH]; intros i mi x14 x15 x16 Hk Hi Hsd I.
  - subst i. change (Z.of_nat 0) with 0 in *. pose proof I as (I1 & I2 & WR & MU & WM & MI).
    pose proof (I2 0 ltac:(lia)) as B0. rewrite Z.add_0_r in B0. pose proof (ro_C1_of_bytes mi s _ B0) as CB0.
    assert (SOK : store_ok bsegs mi (wa d) 1 = true) by (pose proof (wr_at_store_ok bsegs mi d n 0 1 WR ltac:(lia) ltac:(cbn; lia)) as X; rewrite Z.add_0_r in X; exact X).
    assert (EU1 : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
    pose proof (inv_store (0 + 1) n 0 (0 + 1) 0 n 0 0 mi 0 I ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) ltac:(intros j Hj; lia)) as I'.
    rewrite Z.add_0_r in I'.
    zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z_to_bv 64 (bv_unsigned (B 0))) with (zxb (B 0)). rewrite le1_zxb. change (Z_to_bv 64 d) with (wa d).
    zstep. if_false.
    exact (imm_done _ _ _ _ _ _ _ _ _ I').
  - pose proof I as (I1 & I2 & WR & MU & WM & MI).
    assert (Hi0 : 1 <= i) by lia.
    pose proof (ro_C1_of_bytes mi (s + i) _ (I2 i ltac:(lia))) as CB0.
    assert (SOK : store_ok bsegs mi (wa (d + i)) 1 = true) by (apply (wr_at_store_ok bsegs mi d n i 1 WR); cbn; lia).
    assert (EU1 : bv_unsigned (Z_to_bv 64 (s + i)) = s + i) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (d + i)) = d + i) by (apply unsigned_lit; lia).
    pose proof (inv_store (i + 1) n 0 (i + 1) (i - 1 + 1) n 0 (i - 1 + 1) mi i I ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) ltac:(intros j Hj; lia)) as I'.
    set (cs := s + i) in *. set (cd := d + i) in *.
    zstep. change (Z_to_bv 64 (s + i)) with (Z_to_bv 64 cs).
    zstep.
    zstep. change (Z_to_bv 64 (d + i)) with (Z_to_bv 64 cd).
    zstep. zstep. zstep.
    change (Z_to_bv 64 (bv_unsigned (B i))) with (zxb (B i)). rewrite le1_zxb. change (Z_to_bv 64 cd) with (wa cd).
    zstep.
    assert (EU3 : bv_unsigned (Z_to_bv 64 (i + 1)) = i + 1) by (apply unsigned_lit; lia).
    if_true.
    replace (i + -1) with (i - 1) by lia.
    apply (IH (i - 1)); [lia | lia | exact Hsd | exact I'].
Qed.

Corollary imm_fwd0 : forall (mi : mem) x14 x15 x16, 1 <= n -> d < s -> INV 0 0 0 n mi ->
  evt bsegs POST (ST 0x920e0 mi (Z_to_bv 64 s) (Z_to_bv 64 (d + n)) (Z_to_bv 64 d) x14 x15 x16).
Proof using D0 S0 DH SH.
  intros mi x14 x15 x16 Hn Hds I. pose proof (imm_fwd (Z.to_nat (n - 1)) 0 mi x14 x15 x16 ltac:(lia) ltac:(lia) Hds I) as X.
  rewrite !Z.add_0_r in X. exact X.
Qed.

Lemma imm_spec_s : forall x13 x14 x15 x16,
  bytes_at bsegs m s bs -> wr_at bsegs m d n -> mem_inv bsegs m ->
  evt bsegs POST (ST 0x920d0 m (Z_to_bv 64 s) (Z_to_bv 64 n) x13 x14 x15 x16).
Proof using D0 S0 DH SH.
  intros x13 x14 x15 x16 SRC WR MI.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (I0 : forall lo hi slo shi, hi <= lo -> 0 <= slo -> shi <= n -> INV lo hi slo shi m).
  { intros lo hi slo shi H1 H2 H3. split; [intros j Hj; lia|]. split; [intros j Hj; apply bytes_at_nth; [exact SRC | lia]|].
    split; [exact WR|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI]. }
  assert (DONE0 : forall pc x11 x12 x13' x14' x15' x16', (n = 0 \/ d = s) ->
            evt bsegs POST (ST pc m x11 x12 x13' x14' x15' x16') -> evt bsegs POST (ST pc m x11 x12 x13' x14' x15' x16')) by (intros; assumption).
  zstep. if_cases K; zify_cond K.
  -
    zstep. if_cases K2; zify_cond K2.
    +
      assert (Eds : d = s) by lia.
      zstep. apply evt_done. unfold imm_post. do 6 eexists. exists m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI | rewrite Eds; exact SRC].
    + zstep. if_cases K3; zify_cond K3.
      *
        assert (E0 : n = 0) by lia.
        zstep. apply evt_done. unfold imm_post. do 6 eexists. exists m. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
        destruct bs; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | cbn [length] in E0; lia].
      * zstep. zstep.
        apply (imm_bwd (Z.to_nat (n - 1)) (n + -1)); [lia | lia | lia|].
        apply I0; lia.
  -
    zstep. if_cases K3; zify_cond K3.
    + assert (E0 : n = 0) by lia.
      zstep. apply evt_done. unfold imm_post. do 6 eexists. exists m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
      destruct bs; [split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]] | cbn [length] in E0; lia].
    + zstep. zstep.
      apply imm_fwd0; [lia | lia|].
      apply I0; lia.
Qed.

End Proofs.

Lemma imm_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (bs : list byte),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length bs) < 2 ^ 63 -> s + Z.of_nat (length bs) < 2 ^ 63 ->
  bytes_at bsegs m s bs -> wr_at bsegs m d (Z.of_nat (length bs)) -> mem_inv bsegs m ->
  evt bsegs (imm_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc d bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 imm_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until bs. intros -> -> -> D0 S0 DH SH SRC WR MI.
  exact (imm_spec_s ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs D0 S0 DH SH a3 a4 a5 a6 SRC WR MI).
Qed.
