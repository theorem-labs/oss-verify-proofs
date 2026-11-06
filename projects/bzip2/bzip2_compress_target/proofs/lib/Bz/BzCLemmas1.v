(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzLemmasT BzLemmasMtf.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma crc32_table_length : length crc32_table = 256%nat.
Proof. reflexivity. Qed.

Lemma crc32_table_range : Forall (fun w => 0 <= w < 4294967296) crc32_table.
Proof. apply Forall_forall. intros w Hw. apply (proj1 (forallb_forall (fun w => (0 <=? w) && (w <? 4294967296)) crc32_table)) in Hw.
  - apply andb_prop in Hw. destruct Hw as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - vm_compute. reflexivity.
Qed.

Lemma crc32_tbl_range : forall i, 0 <= crc32_tbl i < 4294967296.
Proof.
  intros i. unfold crc32_tbl.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length crc32_table)) as [L|G].
  - apply (proj1 (Forall_nth _ _) crc32_table_range). exact L.
  - rewrite nth_overflow by exact G. lia.
Qed.

Lemma crc_update_range : forall crc ch, 0 <= crc -> 0 <= crc_update crc ch < 4294967296.
Proof.
  intros crc ch Hc. unfold crc_update. change 4294967296 with (2 ^ 32). apply lxor_lt_pow2.
  - pose proof (Z.mod_pos_bound (Z.shiftl crc 8) 4294967296 ltac:(lia)). change (2 ^ 32) with 4294967296. lia.
  - change (2 ^ 32) with 4294967296. apply crc32_tbl_range.
Qed.

Lemma crc_update_n_range : forall n crc ch, 0 <= crc < 4294967296 -> 0 <= crc_update_n crc ch n < 4294967296.
Proof. induction n; intros crc ch H; cbn; [exact H|]. apply IHn. apply crc_update_range. lia. Qed.

Lemma crc_init_range : 0 <= crc_init < 4294967296. Proof. unfold crc_init. lia. Qed.
Lemma crc_final_range : forall c, 0 <= c < 4294967296 -> 0 <= crc_final c < 4294967296.
Proof. intros c H. unfold crc_final. change 4294967296 with (2 ^ 32). apply lxor_lt_pow2; change (2 ^ 32) with 4294967296; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bw_ok (b : bw) : Prop := 0 <= bw_buff b < 4294967296 /\ 0 <= bw_live b <= 32 /\ 0 <= bw_numZ b.

Lemma bw_emit_shape : forall b, bw_live (bw_emit b) = bw_live b - 8 /\ bw_numZ (bw_emit b) = bw_numZ b + 1 /\
  0 <= bw_buff (bw_emit b) < 4294967296.
Proof. intros b. unfold bw_emit. cbn [bw_live bw_numZ bw_buff]. pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)). repeat split; lia. Qed.

(* [comment removed for export] *)
Lemma bw_emit_byte : forall b, 0 <= bw_buff b < 4294967296 -> 0 <= Z.shiftr (bw_buff b) 24 < 256.
Proof. intros b H. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]]. change (2 ^ 24 * 256) with 4294967296. lia. Qed.

(* [comment removed for export] *)
Lemma bs_needw_post : forall f b, bw_ok b -> bw_live b < 8 * Z.of_nat f ->
  bw_ok (bs_needw f b) /\ bw_live (bs_needw f b) = bw_live b mod 8 /\ bw_numZ b <= bw_numZ (bs_needw f b).
Proof.
  induction f as [|f IH]; intros b OK Hf.
  - cps_destruct OK as (A & B & C). cbn in Hf. lia.
  - cbn [bs_needw]. destruct (Z.leb_spec 8 (bw_live b)) as [L|L].
    + cps_destruct (bw_emit_shape b) as (E1 & E2 & E3). cps_pose OK as (A & B & C).
      cps_destruct (IH (bw_emit b)) as (OK' & M & N); [unfold bw_ok; rewrite E1, E2; lia | rewrite E1; lia |].
      split; [exact OK'|]. rewrite M, E1. split; [|rewrite E2 in N; lia].
      replace (bw_live b) with ((bw_live b - 8) + 1 * 8) at 2 by lia. rewrite Z_mod_plus_full. reflexivity.
    + cps_pose OK as (A & B & C). split; [exact OK|]. split; [|lia]. symmetry. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma bsW_facts : forall b n v, bw_ok b -> 1 <= n <= 24 -> 0 <= v ->
  let b1 := bs_needw BS_FUEL b in
  1 <= 32 - bw_live b1 - n <= 31 /\
  bw_ok (bsW b n v) /\ bw_live (bsW b n v) = bw_live b mod 8 + n /\ bw_numZ b <= bw_numZ (bsW b n v).
Proof.
  intros b n v OK Hn Hv. cbv zeta.
  cps_destruct (bs_needw_post BS_FUEL b OK) as (OK1 & M & N); [cps_destruct OK as (A & B & C); unfold BS_FUEL; cbn; lia|].
  pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
  split; [rewrite M; lia|].
  unfold bsW. cps_destruct OK1 as (A1 & B1 & C1).
  split; [| split; [cbn [bw_live]; rewrite M; reflexivity | cbn [bw_numZ]; exact N]].
  unfold bw_ok; cbn [bw_buff bw_live bw_numZ bw_zb]. split; [| rewrite M; lia].
  change 4294967296 with (2 ^ 32). apply lor_lt_pow2; change (2 ^ 32) with 4294967296; [lia|].
  apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)

Lemma bsPutUInt32_ok : forall b u, bw_ok b -> bw_ok (bsPutUInt32 b u).
Proof.
  intros b u OK. unfold bsPutUInt32.
  assert (L : forall x, 0 <= Z.land x 255) by (intros; apply Z.land_nonneg; right; lia).
  cps_destruct (bsW_facts b 8 (Z.land (Z.shiftr u 24) 255) OK ltac:(lia) (L _)) as (_ & OK1 & _).
  cps_destruct (bsW_facts _ 8 (Z.land (Z.shiftr u 16) 255) OK1 ltac:(lia) (L _)) as (_ & OK2 & _).
  cps_destruct (bsW_facts _ 8 (Z.land (Z.shiftr u 8) 255) OK2 ltac:(lia) (L _)) as (_ & OK3 & _).
  cps_destruct (bsW_facts _ 8 (Z.land u 255) OK3 ltac:(lia) (L _)) as (_ & OK4 & _). exact OK4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bs_finish_live : forall f b, bw_live b <= 8 * Z.of_nat f -> bw_live (bs_finish f b) <= 0.
Proof.
  induction f as [|f IH]; intros b H; cbn [bs_finish]; [cbn in H; lia|].
  destruct (Z.ltb_spec 0 (bw_live b)) as [L|L]; [|lia].
  apply IH. destruct (bw_emit_shape b) as (E1 & _). rewrite E1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rl_ok (r : rlst) : Prop :=
  0 <= rl_nblock r /\ 0 <= rl_crc r < 4294967296 /\
  0 <= rl_len r <= 255 /\ 0 <= rl_ch r <= 256 /\ (0 < rl_len r -> rl_ch r < 256).

(* [comment removed for export] *)

Lemma add_pair_to_block_shape : forall r, rl_ok r -> 1 <= rl_len r ->
  rl_ok (add_pair_to_block r) /\
  rl_nblock r + 1 <= rl_nblock (add_pair_to_block r) <= rl_nblock r + 5 /\
  rl_ch (add_pair_to_block r) = rl_ch r /\ rl_len (add_pair_to_block r) = rl_len r.
Proof.
  intros r OK Hl. cps_destruct OK as (A & B & C & D & E).
  pose proof (crc_update_n_range (Z.to_nat (rl_len r)) (rl_crc r) (Z.land (rl_ch r) 255) B) as CR.
  unfold add_pair_to_block.
  destruct (Z.eqb_spec (rl_len r) 1) as [E1|N1]; [cbn; unfold rl_ok; cbn; repeat split; try lia|].
  destruct (Z.eqb_spec (rl_len r) 2) as [E2|N2]; [cbn; unfold rl_ok; cbn; repeat split; try lia|].
  destruct (Z.eqb_spec (rl_len r) 3) as [E3|N3]; [cbn; unfold rl_ok; cbn; repeat split; try lia|].
  cbn. unfold rl_ok; cbn. repeat split; try lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rl_inv (r : rlst) : Prop := rl_ok r /\ (rl_ch r < 256 -> 1 <= rl_len r).

Lemma add_char_to_block_inv : forall r c, rl_inv r -> 0 <= c < 256 ->
  rl_inv (add_char_to_block r c) /\
  rl_nblock r <= rl_nblock (add_char_to_block r c) <= rl_nblock r + 5.
Proof.
  intros r c [OK P] Hc. cps_pose OK as (A & B & C & D & E). unfold add_char_to_block.
  destruct (negb (c =? rl_ch r) && (rl_len r =? 1)) eqn:K1.
  - apply andb_prop in K1. destruct K1 as [K1a K1b]. apply Z.eqb_eq in K1b.
    pose proof (crc_update_range (rl_crc r) (Z.land (rl_ch r) 255) ltac:(lia)).
    unfold rl_inv, rl_ok; cbn. repeat split; try lia.
  - destruct (negb (c =? rl_ch r) || (rl_len r =? 255)) eqn:K2.
    + destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
      * cps_destruct (add_pair_to_block_shape r OK ltac:(lia)) as (OK' & N & Ech & Elen).
        cps_destruct OK' as (A' & B' & C' & D' & E').
        unfold rl_inv, rl_ok; cbn. repeat split; try lia.
      * unfold rl_inv, rl_ok; cbn. repeat split; try lia.
    + apply Bool.orb_false_elim in K2. destruct K2 as [K2a K2b]. apply Bool.negb_false_iff in K2a. apply Z.eqb_eq in K2a. apply Z.eqb_neq in K2b.
      unfold rl_inv, rl_ok; cbn. repeat split; try lia.
Qed.

Lemma init_RL_inv : forall r, rl_ok r -> rl_inv (init_RL r).
Proof. (intros r; cps_intros (A & B & C & D & E)). unfold rl_inv, rl_ok, init_RL; cbn. repeat split; try lia. Qed.

Lemma flush_RL_inv : forall r, rl_inv r ->
  rl_inv (flush_RL r) /\ rl_nblock r <= rl_nblock (flush_RL r) <= rl_nblock r + 5 /\ isempty_RL (flush_RL r) = true.
Proof.
  intros r [OK P]. unfold flush_RL. destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
  - cps_destruct (add_pair_to_block_shape r OK ltac:(lia)) as (OK' & N & _).
    split; [apply init_RL_inv; exact OK'|]. unfold init_RL, isempty_RL; cbn. split; [lia| reflexivity].
  - split; [apply init_RL_inv; exact OK|]. unfold init_RL, isempty_RL; cbn. split; [lia| reflexivity].
Qed.

Lemma inUse_clear_spec : forall n a i j, zget (inUse_clear a i n) j = (if (i <=? j) && (j <? i + Z.of_nat n) then 0 else zget a j).
Proof.
  induction n as [|n IH]; intros a i j.
  - cbn [inUse_clear Z.of_nat]. destruct (Z.leb_spec i j); cbn [andb]; [|reflexivity].
    replace (j <? i + 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - cbn [inUse_clear]. rewrite IH, zget_zset. rewrite Nat2Z.inj_succ. set (m := Z.of_nat n) in *.
    destruct (Z.eqb_spec j i) as [->|NE].
    + replace (i + 1 <=? i) with false by (symmetry; apply Z.leb_gt; lia).
      replace (i <=? i) with true by (symmetry; apply Z.leb_le; lia).
      replace (i <? i + Z.succ m) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + destruct (Z.leb_spec (i + 1) j), (Z.leb_spec i j), (Z.ltb_spec j (i + 1 + m)), (Z.ltb_spec j (i + Z.succ m)); cbn [andb]; try reflexivity; lia.
Qed.

Lemma prepare_new_block_rl_inv : forall r, rl_inv r -> rl_inv (prepare_new_block_rl r) /\ rl_nblock (prepare_new_block_rl r) = 0 /\
  forall j, 0 <= j < 256 -> zget (rl_inUse (prepare_new_block_rl r)) j = 0.
Proof.
  intros r [(A & B & C & D & E) P]. unfold prepare_new_block_rl, rl_inv, rl_ok; cbn [rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len].
  pose proof crc_init_range.
  repeat split; try lia. intros j Hj. rewrite inUse_clear_spec.
  destruct (Z.leb_spec 0 j), (Z.ltb_spec j (0 + Z.of_nat 256)); cbn [andb]; try reflexivity; cbn in *; lia.
Qed.
