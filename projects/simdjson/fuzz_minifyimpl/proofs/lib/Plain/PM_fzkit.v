(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec RegsEquiv.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PIosRegs PIosKitA PIosKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3.AX2. Import AxSymExec3Sound.AX2S. Import AxSymRun3.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma scheck_k_vars : forall segs IT fuel stops ss W pcF srF knF exports wexports,
  scheck_k segs IT fuel stops ss W pcF srF knF exports wexports = true -> kn_vars_lt (s_next ss) knF = true.
Proof.
  intros segs IT fuel stops ss W pcF srF knF exports wexports H. unfold scheck_k in H.
  destruct (srun segs IT fuel stops ss) as [[ss' lg]|]; [|discriminate].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H.
Qed.

Lemma kn_vars_lt_keep : forall b KEEP kn, kn_vars_lt b kn = true -> kn_vars_lt b (kn_keep KEEP kn) = true.
Proof.
  intros b KEEP kn. unfold kn_keep. induction kn as [|k r IH]; intros H; [reflexivity|].
  cbn [kn_vars_lt] in H. apply andb_prop in H as [Hk Hr]. cbn [List.filter].
  destruct (k_keep KEEP k); [cbn [kn_vars_lt]; rewrite Hk, (IH Hr); reflexivity| exact (IH Hr)].
Qed.

Lemma know_ok_app : forall segs E m a b, know_ok segs E m a -> know_ok segs E m b -> know_ok segs E m (a ++ b).
Proof. intros segs E m a b Ha Hb. unfold know_ok in *. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Lemma env_agree_app : forall (l l' : list word) f, env_agree (length l) (Env (vals_ev l) f) (Env (vals_ev (l ++ l')) f).
Proof.
  intros l l' f. split; [| reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev. rewrite app_nth1 by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_add_lit : forall (x : word) (z : Z), 0 <= bv_unsigned x + z < 2^64 ->
  alu64 ALU_ADD x (Z_to_bv 64 z) = Z_to_bv 64 (bv_unsigned x + z).
Proof.
  intros x z Hz. apply bv_eq. rewrite u_add64, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma edenot_add_lit : forall E e z, 0 <= bv_unsigned (edenot E e) + z < 2^64 ->
  edenot E (EAlu ALU_ADD e (ELit z)) = Z_to_bv 64 (bv_unsigned (edenot E e) + z).
Proof. intros E e z Hz. cbn [edenot]. apply u_add_lit. exact Hz. Qed.

Lemma unsigned_lit64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.
Notation mem := (word -> option byte).

Lemma wr_at_of_stk : forall (m : mem) lo hi A n, stk segs m lo hi -> lo <= A -> A + n <= hi -> wr_at segs m A n.
Proof.
  intros m lo hi A n (S1 & S2 & S3) H1 H2. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (S3 (A + i) ltac:(lia))).
Qed.

Lemma wr_at_window : forall (m : mem) (L H : Z) A n,
  (forall x : word, L <= bv_unsigned x < H -> wview segs m x <> None) ->
  L <= A -> A + n <= H -> 0 <= L -> H <= 2^64 -> wr_at segs m A n.
Proof.
  intros m L H A n W H1 H2 H3 H4. split; [lia|]. split; [lia|]. intros i Hi. apply W. unfold wa. rewrite unsigned_lit64 by lia. lia.
Qed.

Lemma wr_at_sub : forall (m : mem) A n A' n', wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  intros m A n A' n' (W1 & W2 & W3) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A' + i) with (A + (A' - A + i)) by lia. apply W3. lia.
Qed.

Lemma wview_of_wr_at : forall (m : mem) A n (x : word), wr_at segs m A n -> A <= bv_unsigned x < A + n -> wview segs m x <> None.
Proof.
  intros m A n x (W1 & W2 & W3) Hx. specialize (W3 (bv_unsigned x - A) ltac:(lia)).
  replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in W3 by lia. unfold wa in W3. rewrite Z_to_bv_bv_unsigned in W3. exact W3.
Qed.

Lemma rw_cells_C8_of_bytes : forall (m : mem) A (v : word),
  bytes_at segs m A (word_to_le_bytes 8 v) -> wr_at segs m A 8 -> rw_cells segs m A [C8 v].
Proof.
  intros m A v HB HW. split; [split; [cbn; auto|]| cbn [cells_size csize Nat.add]; exact HW].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
Qed.

Lemma rw_cells_C4_of_bytes : forall (m : mem) A (v : word),
  bytes_at segs m A (word_to_le_bytes 4 v) -> wr_at segs m A 4 -> rw_cells segs m A [C4 v].
Proof.
  intros m A v HB HW. split; [split; [cbn; auto|]| cbn [cells_size csize Nat.add]; exact HW].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
Qed.

Lemma rw_cells_CB_of_bytes : forall (m : mem) A (bs : list byte),
  bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) -> rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs HB HW. split; [split; [cbn; auto|]| cbn [cells_size csize]; rewrite Nat.add_0_r; exact HW].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
Qed.

Lemma rw_cells_cons : forall (m : mem) A c cs,
  rw_cells segs m A [c] -> rw_cells segs m (A + Z.of_nat (csize c)) cs -> rw_cells segs m A (c :: cs).
Proof.
  intros m A c cs [[W1 B1] R1] [[W2 B2] R2]. cbn [cells_wf] in W1. destruct W1 as [W1 _].
  cbn [cells_bytes] in B1. rewrite app_nil_r in B1. cbn [cells_size] in R1. rewrite Nat.add_0_r in R1.
  pose proof (cbytes_length c W1) as L1.
  split; [split; [cbn; split; [exact W1| exact W2]|]|].
  - cbn [cells_bytes]. destruct B1 as (B1a & B1b & B1c). destruct B2 as (B2a & B2b & B2c).
    split; [lia|]. split; [rewrite length_app; lia|].
    intros i Hi. rewrite length_app in Hi. destruct (Nat.lt_ge_cases i (length (cbytes c))) as [Hl|Hg].
    + rewrite nth_error_app1 by exact Hl. apply B1c. exact Hl.
    + rewrite nth_error_app2 by exact Hg. rewrite <- (B2c (i - length (cbytes c))%nat ltac:(lia)). f_equal. f_equal. lia.
  - cbn [cells_size]. destruct R1 as (R1a & R1b & R1c). destruct R2 as (R2a & R2b & R2c). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (csize c))) as [Hl|Hg]; [apply R1c; lia|].
    replace (A + i) with (A + Z.of_nat (csize c) + (i - Z.of_nat (csize c))) by lia. apply R2c. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_agree : forall (m m' : mem) A bs,
  (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) -> bytes_at segs m A bs -> bytes_at segs m' A bs.
Proof.
  intros m m' A bs HA (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|]. intros i Hi.
  unfold mrd. rewrite (HA (A + Z.of_nat i) ltac:(lia)). apply B3. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma kn_word_C8 : forall E (m : mem) A (v : word) e cs,
  rw_cells segs m A (C8 v :: cs) -> edenot E e = v -> kentry_ok segs E m (KWord (SA (ELit 0) A) 8 e).
Proof.
  intros E m A v e cs [[Hwf HB] _] He. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB as [HB _].
  apply (kn_word segs E m A 8 e (le8 v) HB); [reflexivity | lia | rewrite He; reflexivity].
Qed.
Lemma kn_word_C4 : forall E (m : mem) A (v : word) e cs,
  rw_cells segs m A (C4 v :: cs) -> edenot E e = v -> kentry_ok segs E m (KWord (SA (ELit 0) A) 4 e).
Proof.
  intros E m A v e cs [[Hwf HB] _] He. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB as [HB _].
  apply (kn_word segs E m A 4 e (le4 v) HB); [reflexivity | lia | rewrite He; reflexivity].
Qed.
Lemma rw_cells_tl : forall (m : mem) A c cs, rw_cells segs m A (c :: cs) -> rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[W B] R]. cbn [cells_wf] in W. destruct W as [W1 W2]. pose proof (cbytes_length c W1) as L1.
  cbn [cells_bytes] in B. apply bytes_at_app in B as [_ B]. rewrite L1 in B.
  cbn [cells_size] in R. destruct R as (R1 & R2 & R3).
  split; [split; [exact W2| exact B]|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply R3. lia.
Qed.
End WithSegs.
