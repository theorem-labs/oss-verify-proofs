(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 BzCMtf BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpSess CmpSess2 CmpWS.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rl_pot (r : rlst) : Z := 4 * rl_nblock r + 5 * rl_len r.

Lemma add_pair_pot : forall r, rl_ok r -> 1 <= rl_len r ->
  4 * rl_nblock (add_pair_to_block r) <= 4 * rl_nblock r + 5 * rl_len r /\ (rl_len r <= 3 -> rl_nblock (add_pair_to_block r) = rl_nblock r + rl_len r).
Proof.
  intros r OK Hl. unfold add_pair_to_block.
  destruct (Z.eqb_spec (rl_len r) 1) as [E1|N1]; [cbn; lia|].
  destruct (Z.eqb_spec (rl_len r) 2) as [E2|N2]; [cbn; lia|].
  destruct (Z.eqb_spec (rl_len r) 3) as [E3|N3]; [cbn; lia|].
  cbn. lia.
Qed.

Lemma add_char_pot : forall r c, rl_inv r -> 0 <= c < 256 -> rl_pot (add_char_to_block r c) <= rl_pot r + 5.
Proof.
  intros r c [OK P] Hc. cps_pose OK as (A & B & C & D & E). unfold add_char_to_block, rl_pot.
  destruct (negb (c =? rl_ch r) && (rl_len r =? 1)) eqn:K1.
  - apply andb_prop in K1. destruct K1 as [_ K1b]. apply Z.eqb_eq in K1b. cbn. lia.
  - destruct (negb (c =? rl_ch r) || (rl_len r =? 255)) eqn:K2.
    + destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
      * assert (Hl : 1 <= rl_len r) by (apply P; exact L).
        pose proof (add_pair_pot r OK Hl) as [X _]. cbn [rl_nblock rl_len]. lia.
      * cbn [rl_nblock rl_len]. lia.
    + cbn. lia.
Qed.

Lemma flush_pot : forall r, rl_inv r -> rl_pot (flush_RL r) <= rl_pot r /\ rl_len (flush_RL r) = 0.
Proof.
  intros r [OK P]. cps_pose OK as (A & B & C & D & E). unfold flush_RL, init_RL, rl_pot. cbn [rl_nblock rl_len].
  destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
  - pose proof (add_pair_pot r OK (P L)) as [X _]. lia.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inuse01 (iu : zarr) : Prop := forall i, 0 <= i < 256 -> zget iu i = 0 \/ zget iu i = 1.
Definition blk_iu (nb : Z) (blk iu : zarr) : Prop := forall j, 0 <= j < nb -> zget iu (zget blk j) = 1.
Definition RLX (r : rlst) : Prop :=
  rl_inv r /\ zbok (rl_block r) /\ zdefr (rl_inUse r) 0 256 /\ inuse01 (rl_inUse r) /\ blk_iu (rl_nblock r) (rl_block r) (rl_inUse r).

Lemma inuse01_set1 : forall iu i, inuse01 iu -> inuse01 (zset iu i 1).
Proof. intros iu i H k Hk. rewrite zget_zset. destruct (k =? i); [right; reflexivity| apply H; exact Hk]. Qed.
Lemma blk_iu_set1 : forall nb blk iu i, blk_iu nb blk iu -> blk_iu nb blk (zset iu i 1).
Proof. intros nb blk iu i H j Hj. rewrite zget_zset. destruct (zget blk j =? i); [reflexivity| apply H; exact Hj]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land255_small : forall b, 0 <= b < 256 -> Z.land b 255 = b.
Proof. intros b Hb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Definition PUTI (q : rlst) : Prop := 0 <= rl_nblock q /\ zbok (rl_block q) /\ blk_iu (rl_nblock q) (rl_block q) (rl_inUse q).
Lemma put_ok : forall q b, 0 <= b < 256 -> PUTI q -> zget (rl_inUse q) b = 1 ->
  PUTI (rl_put q b) /\ rl_inUse (rl_put q b) = rl_inUse q /\ rl_nblock (rl_put q b) = rl_nblock q + 1 /\
  rl_ch (rl_put q b) = rl_ch q /\ rl_len (rl_put q b) = rl_len q /\ rl_crc (rl_put q b) = rl_crc q.
Proof.
  (intros q b Hb; cps_intros (Q1 & Q2 & Q3); intros G). unfold rl_put, PUTI; cbn [rl_nblock rl_block rl_inUse rl_ch rl_len rl_crc].
  rewrite (land255_small b Hb). split; [| repeat split; reflexivity].
  split; [lia|]. split; [apply zbok_zset; [exact Q2| lia]|].
  intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j (rl_nblock q)) as [->|NE]; [exact G|]. apply Q3. lia.
Qed.

Lemma add_pair_RLX : forall r, RLX r -> 1 <= rl_len r ->
  RLX (add_pair_to_block r) /\ rl_nblock r + 1 <= rl_nblock (add_pair_to_block r) <= rl_nblock r + 5 /\
  rl_ch (add_pair_to_block r) = rl_ch r /\ rl_len (add_pair_to_block r) = rl_len r.
Proof.
  (intros r; cps_intros (INV & BOK & DEF & U01 & BI); intros Hl). pose proof INV as [OK P]. cps_pose OK as (A & B & C & D & E).
  cps_pose (add_pair_to_block_shape r OK Hl) as (OK' & NB & ECH & ELEN).
  split; [| split; [exact NB| split; [exact ECH| exact ELEN]]].
  split; [split; [exact OK'| rewrite ECH, ELEN; exact P]|].
  (* [comment removed for export] *)
  assert (CHR : 0 <= rl_ch r < 256) by lia.
  unfold add_pair_to_block. rewrite (land255_small _ CHR). cbv zeta.
  set (r1 := RL (rl_nblock r) (rl_block r) (zset (rl_inUse r) (rl_ch r) 1) (crc_update_n (rl_crc r) (rl_ch r) (Z.to_nat (rl_len r))) (rl_ch r) (rl_len r)).
  assert (R1 : PUTI r1 /\ zget (rl_inUse r1) (rl_ch r) = 1 /\ zdefr (rl_inUse r1) 0 256 /\ inuse01 (rl_inUse r1)).
  { subst r1; unfold PUTI; cbn [rl_nblock rl_block rl_inUse]. split; [split; [lia| split; [exact BOK| apply blk_iu_set1; exact BI]]|].
    split; [rewrite zget_zset_same; reflexivity|]. split; [apply zdefr_mono; exact DEF| apply inuse01_set1; exact U01]. }
  assert (L1 : rl_len r1 = rl_len r) by reflexivity. assert (N1 : rl_nblock r1 = rl_nblock r) by reflexivity.
  clearbody r1. cps_destruct R1 as (P1 & G1 & D1 & U1).
  (* [comment removed for export] *)
  assert (STEP : forall q, PUTI q -> rl_inUse q = rl_inUse r1 -> PUTI (rl_put q (rl_ch r)) /\ rl_inUse (rl_put q (rl_ch r)) = rl_inUse r1).
  { intros q Pq Iq. cps_destruct (put_ok q (rl_ch r) CHR Pq ltac:(rewrite Iq; exact G1)) as (X1 & X2 & _). split; [exact X1| rewrite X2; exact Iq]. }
  destruct (Z.eqb_spec (rl_len r) 1) as [E1|N1'].
  { cbn [Z.sub]. destruct (STEP r1 P1 eq_refl) as [[X1 [X2 X3]] X4]. rewrite <- X4 in D1, U1. exact (conj X2 (conj D1 (conj U1 X3))). }
  destruct (Z.eqb_spec (rl_len r) 2) as [E2|N2].
  { cbn [Z.sub]. destruct (STEP r1 P1 eq_refl) as [Y1 Y4]. destruct (STEP _ Y1 Y4) as [[X1 [X2 X3]] X4]. rewrite <- X4 in D1, U1. exact (conj X2 (conj D1 (conj U1 X3))). }
  destruct (Z.eqb_spec (rl_len r) 3) as [E3|N3].
  { cbn [Z.sub]. destruct (STEP r1 P1 eq_refl) as [Y1 Y4]. destruct (STEP _ Y1 Y4) as [W1 W4]. destruct (STEP _ W1 W4) as [[X1 [X2 X3]] X4].
    rewrite <- X4 in D1, U1. exact (conj X2 (conj D1 (conj U1 X3))). }
  cbn [Z.sub].
  (* [comment removed for export] *)
  set (r2 := RL (rl_nblock r1) (rl_block r1) (zset (rl_inUse r1) (rl_len r - 4) 1) (rl_crc r1) (rl_ch r1) (rl_len r1)).
  assert (LR : 0 <= rl_len r - 4 < 256) by lia.
  assert (R2 : PUTI r2 /\ zget (rl_inUse r2) (rl_ch r) = 1 /\ zget (rl_inUse r2) (rl_len r - 4) = 1 /\ zdefr (rl_inUse r2) 0 256 /\ inuse01 (rl_inUse r2)).
  { subst r2; unfold PUTI; cbn [rl_nblock rl_block rl_inUse]. cps_destruct P1 as (P1a & P1b & P1c).
    split; [split; [exact P1a| split; [exact P1b| apply blk_iu_set1; exact P1c]]|].
    split; [rewrite zget_zset; destruct (rl_ch r =? rl_len r - 4); [reflexivity| exact G1]|].
    split; [rewrite zget_zset_same; reflexivity|]. split; [apply zdefr_mono; exact D1| apply inuse01_set1; exact U1]. }
  clearbody r2. cps_destruct R2 as (P2 & G2 & G2' & D2 & U2).
  assert (STEP2 : forall q, PUTI q -> rl_inUse q = rl_inUse r2 -> PUTI (rl_put q (rl_ch r)) /\ rl_inUse (rl_put q (rl_ch r)) = rl_inUse r2).
  { intros q Pq Iq. cps_destruct (put_ok q (rl_ch r) CHR Pq ltac:(rewrite Iq; exact G2)) as (X1 & X2 & _). split; [exact X1| rewrite X2; exact Iq]. }
  destruct (STEP2 r2 P2 eq_refl) as [Y1 Y4]. destruct (STEP2 _ Y1 Y4) as [W1 W4]. destruct (STEP2 _ W1 W4) as [V1 V4]. destruct (STEP2 _ V1 V4) as [T1 T4].
  cps_destruct (put_ok _ (rl_len r - 4) LR T1 ltac:(rewrite T4; exact G2')) as ([X1 [X2 X3]] & X4 & _).
  rewrite <- T4, <- X4 in D2, U2. exact (conj X2 (conj D2 (conj U2 X3))).
Qed.

Lemma add_char_RLX : forall r c, RLX r -> 0 <= c < 256 ->
  RLX (add_char_to_block r c) /\ rl_nblock r <= rl_nblock (add_char_to_block r c) <= rl_nblock r + 5 /\
  rl_pot (add_char_to_block r c) <= rl_pot r + 5 /\
  (rl_nblock r < rl_nblock (add_char_to_block r c) -> rl_len (add_char_to_block r c) = 1).
Proof.
  intros r c X Hc. cps_pose X as (INV & BOK & DEF & U01 & BI). pose proof INV as [OK P]. cps_pose OK as (A & B & C & D & E).
  pose proof (add_char_to_block_inv r c INV Hc) as [INV' NB']. pose proof (add_char_pot r c INV Hc) as POT.
  split; [| split; [exact NB'| split; [exact POT|]]].
  - split; [exact INV'|]. unfold add_char_to_block.
    destruct (negb (c =? rl_ch r) && (rl_len r =? 1)) eqn:K1.
    + (* [comment removed for export] *)
      apply andb_prop in K1. destruct K1 as [K1a K1b]. apply Z.eqb_eq in K1b.
      assert (CHR : 0 <= rl_ch r < 256) by lia. rewrite (land255_small _ CHR). cbn [rl_block rl_inUse rl_nblock].
      split; [apply zbok_zset; [exact BOK| lia]|]. split; [apply zdefr_mono; exact DEF|]. split; [apply inuse01_set1; exact U01|].
      intros j Hj. rewrite !zget_zset. destruct (Z.eqb_spec j (rl_nblock r)) as [->|NE].
      * rewrite Z.eqb_refl. reflexivity.
      * destruct (zget (rl_block r) j =? rl_ch r); [reflexivity|]. apply BI. lia.
    + destruct (negb (c =? rl_ch r) || (rl_len r =? 255)) eqn:K2.
      * destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
        -- destruct (add_pair_RLX r X (P L)) as ((_ & B2 & D2 & U2 & I2) & _). cbn [rl_block rl_inUse rl_nblock].
           exact (conj B2 (conj D2 (conj U2 I2))).
        -- cbn [rl_block rl_inUse rl_nblock]. exact (conj BOK (conj DEF (conj U01 BI))).
      * cbn [rl_block rl_inUse rl_nblock]. exact (conj BOK (conj DEF (conj U01 BI))).
  - unfold add_char_to_block.
    destruct (negb (c =? rl_ch r) && (rl_len r =? 1)) eqn:K1.
    + apply andb_prop in K1. destruct K1 as [_ K1b]. apply Z.eqb_eq in K1b. cbn [rl_nblock rl_len]. lia.
    + destruct (negb (c =? rl_ch r) || (rl_len r =? 255)) eqn:K2; cbn [rl_nblock rl_len]; [reflexivity| lia].
Qed.

Lemma flush_RLX : forall r, RLX r ->
  RLX (flush_RL r) /\ rl_nblock r <= rl_nblock (flush_RL r) <= rl_nblock r + 5 /\ rl_pot (flush_RL r) <= rl_pot r /\
  rl_len (flush_RL r) = 0 /\ rl_ch (flush_RL r) = 256 /\ isempty_RL (flush_RL r) = true.
Proof.
  intros r X. cps_pose X as (INV & BOK & DEF & U01 & BI). pose proof INV as [OK P].
  cps_pose (flush_RL_inv r INV) as (INV' & NB' & EMP). pose proof (flush_pot r INV) as [POT L0].
  split; [| split; [exact NB'| split; [exact POT| split; [exact L0| split; [reflexivity| exact EMP]]]]].
  split; [exact INV'|]. unfold flush_RL, init_RL. cbn [rl_block rl_inUse rl_nblock].
  destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
  - destruct (add_pair_RLX r X (P L)) as ((_ & B2 & D2 & U2 & I2) & _). exact (conj B2 (conj D2 (conj U2 I2))).
  - exact (conj BOK (conj DEF (conj U01 BI))).
Qed.

Lemma prepare_RLX : forall r, rl_inv r -> zbok (rl_block r) -> RLX (prepare_new_block_rl r) /\ rl_nblock (prepare_new_block_rl r) = 0 /\
  rl_len (prepare_new_block_rl r) = rl_len r /\ rl_ch (prepare_new_block_rl r) = rl_ch r /\ rl_block (prepare_new_block_rl r) = rl_block r /\
  rl_crc (prepare_new_block_rl r) = crc_init.
Proof.
  intros r INV BOK. cps_pose (prepare_new_block_rl_inv r INV) as (INV' & NB0 & Z0).
  split; [| split; [exact NB0| repeat split; reflexivity]].
  split; [exact INV'|]. unfold prepare_new_block_rl. cbn [rl_block rl_inUse rl_nblock].
  split; [exact BOK|]. split; [apply inUse_clear_zdefr|]. split.
  - intros i Hi. left. unfold prepare_new_block_rl in Z0. cbn [rl_inUse] in Z0. apply Z0. exact Hi.
  - intros j Hj. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record HCX (cx : cctx) (g : eg) (e : est) (z : zstrm) : Prop := HX {
  hx_ok : est_ok e;
  hx_rl : rl_inv (est_rl e);
  hx_def : zdefr (e_inUse e) 0 256;
  hx_iu : inuse01 (e_inUse e);
  hx_mode : e_mode e = BZ_M_RUNNING \/ (e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = 0 /\ z_avail_in z = 0);
  hx_ain : z_avail_in z = Z.of_nat (length (z_in z));
  hx_inb : Forall (fun c => 0 <= c < 256) (z_in z);
  hx_aout : 0 <= z_avail_out z <= BZ_MAX_UNUSED /\ Z.of_nat (length (z_outr z)) = BZ_MAX_UNUSED - z_avail_out z;
  hx_tin : z_tin_hi z = 0 /\ 0 <= z_tin_lo z /\ z_tin_lo z + z_avail_in z < 67108864;
  hx_pot : 4 * e_nblock e + 5 * e_state_in_len e + 4 * NBLOCKMAX * (e_blockNo e - 1) <= 5 * z_tin_lo z;
  hx_out : e_state e = BZ_S_OUTPUT ->
           g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) /\
           (forall k, 0 <= k < bw_numZ (e_bw e) -> zget (e_arr2 e) (e_nblock e + k) = zget (bw_zb (e_bw e)) k) /\
           (NBLOCKMAX <= e_nblock e \/ (e_mode e = BZ_M_FINISHING /\ isempty_RL_e e = true)) /\ g_bs g = true;
  hx_numZ : e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE;
  hx_in : e_state e = BZ_S_INPUT ->
          bw_numZ (e_bw e) = 0 /\ e_state_out_pos e = 0 /\ e_nblock e <= NBLOCKMAX + 4 /\ blk_iu (e_nblock e) (e_arr2 e) (e_inUse e);
  (* [comment removed for export] *)
  hx_bw : g_bs g = true -> bw_ok (e_bw e) \/ (e_state e = BZ_S_OUTPUT /\ e_mode e = BZ_M_FINISHING /\ isempty_RL_e e = true);
  hx_bs : e_blockNo e = 1 \/ g_bs g = true
}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cb_facts (e : est) : Prop :=
  e_state_out_pos e = 0 /\ bw_numZ (e_bw e) = 0 /\ rl_inv (est_rl e) /\ inuse01 (e_inUse e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cb_entry (g : eg) (e : est) : Prop := cb_pre g e /\ cb_facts e.

Record cbm : Prop := CBM {
  (* [comment removed for export] *)
  cbm_gmf : forall g e, cb_entry g e -> 0 < e_nblock e -> BzCFactsGm.gm_facts (cb_sorted e);
  (* [comment removed for export] *)
  cbm_arrs : forall g e b, cb_entry g e -> let e' := fst (compressBlock e b znew) in
      zbok (e_arr1 e') /\ zbok (e_arr2 e') /\ (forall i, 0 <= zget (e_ftab e') i < 4294967296);
  (* [comment removed for export] *)
  cbm_bw : forall g e, cb_entry g e -> bw_ok (e_bw (fst (compressBlock e false znew)))
}.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cbn_acc :=
  unfold isempty_RL_e in *; unfold est_set_outpos, est_set_rl, est_set_modes, est_set_bw, est_rl in *;
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
       e_rfreq e_len_pack z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi
       fst snd rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len bw_buff bw_live bw_numZ bw_zb] in *.

(* [comment removed for export] *)
Ltac cbn_acc_goal :=
  lazymatch goal with
  | |- ?G =>
      let G1 := eval unfold isempty_RL_e in G in
      let G2 := eval unfold est_set_outpos, est_set_rl, est_set_modes, est_set_bw, est_rl in G1 in
      let G3 := eval cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
       e_rfreq e_len_pack z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi
       fst snd rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len bw_buff bw_live bw_numZ bw_zb] in G2 in
      change_no_check G3
  end.

(* [comment removed for export] *)
Ltac est_ok_from OK :=
  let K1 := fresh "K" in let K2 := fresh "K" in let K3 := fresh "K" in let K4 := fresh "K" in let K5 := fresh "K" in
  let K6 := fresh "K" in let K7 := fresh "K" in let K8 := fresh "K" in let K9 := fresh "K" in let K10 := fresh "K" in
  let K11 := fresh "K" in let K12 := fresh "K" in let K13 := fresh "K" in
  cps_pose OK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13); unfold est_ok in K1;
  unfold est_ok; cbn_acc; repeat apply conj; cbn_acc; try assumption; bz_params; try lia.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)

Lemma m32_small : forall x, 0 <= x < 4294967296 -> m32 x = x.
Proof. intros x Hx. unfold m32. apply Z.mod_small. exact Hx. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma bw_ok_reset : forall b, bw_ok b -> bw_ok (BW (bw_buff b) (bw_live b) 0 znew).
Proof. (intros b; cps_intros (A & B & C)). unfold bw_ok; cbn. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gm_shape : forall e yy, exists arr1 nInUse unseq wr mtfFreq,
  fst (generateMTFValues e yy) =
  EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) nInUse (e_inUse e) unseq
      (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) wr mtfFreq (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Proof.
  intros e yy. unfold generateMTFValues.
  destruct (mk_maps _ _ _ _ _) as [unseq nInUse].
  destruct (gm_loop _ _ _ _ _ _) as [a1 mf y w zp].
  cbn [gm_arr1 gm_mtfFreq gm_yy gm_wr gm_zPend].
  destruct (if 0 <? zp then _ else _) as [[a1' mf'] w'].
  destruct (mtf_emit a1' mf' w' (nInUse + 1)) as [[a1'' mf''] w''].
  cbn [fst]. do 5 eexists. reflexivity.
Qed.

Lemma sm_shape : forall e c0 f0 p0 i0 h0 w0 q0, exists b nMTF sel selMtf len code rfreq lp,
  fst (sendMTFValues e c0 f0 p0 i0 h0 w0 q0) =
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      b (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) nMTF (e_mtfFreq e) sel selMtf len code rfreq lp.
Proof.
  intros. unfold sendMTFValues.
  destruct (sm_selmtf _ _ _ _ _) as [pos selMtf].
  destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b selCtr].
  cbn [fst]. do 8 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cb_shape : forall e is_last, exists arr1 ftab op nInUse unseq nMTF mtfFreq sel selMtf len code rfreq lp,
  let b' := e_bw (fst (compressBlock e is_last znew)) in
  fst (compressBlock e is_last znew) =
  EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 (lay_zbits (if 0 <? e_nblock e then e_arr2 (cb_sorted e) else e_arr2 e) (e_nblock e) (bw_bytes b'))
      ftab op (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) nInUse (e_inUse e) unseq
      b' (if 0 <? e_nblock e then crc_final (e_blockCRC e) else e_blockCRC e)
      (if 0 <? e_nblock e then e_combinedCRC (cb_e0 e) else e_combinedCRC e) (e_blockNo e) nMTF mtfFreq sel selMtf len code rfreq lp.
Proof.
  intros e is_last. cbv zeta. unfold compressBlock, cb_sorted.
  destruct (Z.ltb_spec 0 (e_nblock e)) as [POS|ZERO].
  - replace (blockSort _ znew) with (blockSort (cb_e0 e) znew) by reflexivity.
    cps_destruct (blockSort_shape (cb_e0 e) znew) as (a1 & a2 & ft & op & BS).
    destruct (blockSort (cb_e0 e) znew) as [[[e1 fs] ms] bu]. cbn [fst] in BS |- *. subst e1.
    unfold cb_e0. cbn_acc_goal.
    match goal with |- context [generateMTFValues ?ee znew] => cps_destruct (gm_shape ee znew) as (ga1 & gni & gus & gwr & gmf & GM); destruct (generateMTFValues ee znew) as [eg yy] end.
    cbn [fst] in GM. subst eg. cbn_acc_goal.
    match goal with |- context [sendMTFValues ?ee znew znew znew znew znew znew znew] =>
      cps_destruct (sm_shape ee znew znew znew znew znew znew znew) as (sb & snm & ssel & ssm & sln & scd & srf & slp & SM);
      destruct (sendMTFValues ee znew znew znew znew znew znew znew) as [es sm] end.
    cbn [fst] in SM. subst es. cbn_acc_goal. do 13 eexists. reflexivity.
  - cbn_acc_goal. do 13 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cb_keep : forall e b, let e' := fst (compressBlock e b znew) in
  e_mode e' = e_mode e /\ e_state e' = e_state e /\ e_avail_in_expect e' = e_avail_in_expect e /\ e_nblock e' = e_nblock e /\
  e_state_in_ch e' = e_state_in_ch e /\ e_state_in_len e' = e_state_in_len e /\ e_inUse e' = e_inUse e /\
  e_blockNo e' = e_blockNo e /\ e_state_out_pos e' = e_state_out_pos e /\
  e_blockCRC e' = (if 0 <? e_nblock e then crc_final (e_blockCRC e) else e_blockCRC e) /\
  e_combinedCRC e' = (if 0 <? e_nblock e then e_combinedCRC (cb_e0 e) else e_combinedCRC e) /\
  e_arr2 e' = lay_zbits (if 0 <? e_nblock e then e_arr2 (cb_sorted e) else e_arr2 e) (e_nblock e) (bw_bytes (e_bw e')).
Proof.
  intros e b. cbv zeta.
  cps_destruct (cb_shape e b) as (a1 & ft & op & ni & us & nm & mf & sl & sm & ln & cd & rf & lp & E).
  cbv zeta in E. rewrite E at 1 2 3 4 5 6 7 8 9 10 11 12. cbn_acc. repeat split; reflexivity.
Qed.

Lemma combinedCRC_e0_range : forall e, 0 <= e_blockCRC e < 4294967296 -> 0 <= e_combinedCRC e < 4294967296 ->
  0 <= e_combinedCRC (cb_e0 e) < 4294967296.
Proof.
  intros e HB HC. unfold cb_e0. cbn_acc. change 4294967296 with (2 ^ 32).
  apply BzLemmasMtf.lxor_lt_pow2.
  - apply BzLemmasT.lor_lt_pow2.
    + pose proof (Z.mod_pos_bound (Z.shiftl (e_combinedCRC e) 1) (2 ^ 32) ltac:(lia)). lia.
    + rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 31 * 2 ^ 32) with (2 ^ 63). lia.
  - change (2 ^ 32) with 4294967296. apply crc_final_range. exact HB.
Qed.

(* [comment removed for export] *)
Lemma cb_zbits : forall e b, 0 <= e_nblock e -> let e' := fst (compressBlock e b znew) in
  forall k, 0 <= k < bw_numZ (e_bw e') -> zget (e_arr2 e') (e_nblock e + k) = zget (bw_zb (e_bw e')) k.
Proof.
  intros e b NB. cbv zeta. intros k Hk.
  pose proof (cb_keep e b) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A2). rewrite A2.
  unfold lay_zbits. replace k with (Z.of_nat (Z.to_nat k)) at 1 by lia.
  rewrite zget_of_list_at by (rewrite bw_bytes_length; lia).
  unfold bw_bytes. apply nth_error_nth. rewrite zarr_to_list_nth by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma bsW_ok_any : forall b n v, bw_ok b -> 1 <= n <= 24 -> bw_ok (bsW b n v) /\ bw_numZ b <= bw_numZ (bsW b n v).
Proof.
  intros b n v OK Hn.
  cps_destruct (bs_needw_post BS_FUEL b OK) as (OK1 & M & N); [cps_destruct OK as (A & B & C); unfold BS_FUEL; cbn; lia|].
  pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
  unfold bsW. cps_destruct OK1 as (A1 & B1 & C1). split; [| cbn [bw_numZ]; exact N].
  unfold bw_ok; cbn [bw_buff bw_live bw_numZ bw_zb]. split; [| rewrite M; lia].
  change 4294967296 with (2 ^ 32). apply BzLemmasT.lor_lt_pow2; change (2 ^ 32) with 4294967296; [lia|].
  apply Z.mod_pos_bound. lia.
Qed.
Lemma bsPutUChar_ok_any : forall b c, bw_ok b -> bw_ok (bsPutUChar b c).
Proof. intros. unfold bsPutUChar. apply bsW_ok_any; [assumption| lia]. Qed.

Lemma bits_bhdr : forall b e1, bits (cb_bhdr b e1) = bits b + 105.
Proof. intros. unfold cb_bhdr, bsPutUInt32, bsPutUChar. rewrite !bsW_bits. lia. Qed.
Lemma bhdr_ok : forall b e1, bw_ok b -> bw_ok (cb_bhdr b e1).
Proof.
  intros b e1 OK. unfold cb_bhdr.
  apply bsW_ok_any; [| lia]. apply bsW_ok_any; [| lia]. apply bsPutUInt32_ok. do 6 apply bsPutUChar_ok_any. exact OK.
Qed.
Lemma hdr_ok : forall e1, 0 <= bw_numZ (e_bw e1) -> (e_blockNo e1 = 1 \/ bw_ok (e_bw e1)) -> bw_ok (cb_hdr e1).
Proof.
  intros e1 NZ H. unfold cb_hdr. destruct (Z.eqb_spec (e_blockNo e1) 1) as [E|NE].
  - do 4 apply bsPutUChar_ok_any. unfold bw_ok; cbn [bw_buff bw_live bw_numZ]. lia.
  - destruct H as [H|H]; [congruence| exact H].
Qed.

Lemma bits_nonneg : forall b, bw_ok b -> 0 <= bits b.
Proof. (intros b; cps_intros (A & B & C)). unfold bits. lia. Qed.
Lemma numZ_lower : forall b, bw_ok b -> bits b - 32 <= 8 * bw_numZ b.
Proof. (intros b; cps_intros (A & B & C)). unfold bits. lia. Qed.

(* [comment removed for export] *)
Lemma cb_pos_blk : forall e b, 0 < e_nblock e -> (e_blockNo e = 1 \/ bw_ok (e_bw e)) ->
  1 <= bw_numZ (e_bw (fst (compressBlock e b znew))).
Proof.
  intros e b POS BW. rewrite compressBlock_bw.
  replace (0 <? e_nblock e) with true by (symmetry; apply Z.ltb_lt; exact POS). cbv iota. cbv zeta.
  cps_destruct (cb_sorted_fields e) as (F1 & F2 & F3 & F4). set (e1 := cb_sorted e) in *.
  assert (OK0 : bw_ok (cb_hdr e1)).
  { apply hdr_ok; [rewrite F4; cbn; lia|]. rewrite F2, F4. destruct BW as [BW|BW]; [left; exact BW| right; apply bw_ok_reset; exact BW]. }
  pose proof (bhdr_ok (cb_hdr e1) e1 OK0) as OK1. pose proof (bits_bhdr (cb_hdr e1) e1) as B1.
  pose proof (bits_nonneg _ OK0) as B0. pose proof (numZ_lower _ OK1) as L1.
  set (b1 := cb_bhdr (cb_hdr e1) e1) in *.
  destruct (gm_bw (est_set_bw e1 b1) znew) as [G1 _].
  set (eg := fst (generateMTFValues (est_set_bw e1 b1) znew)) in *.
  pose proof (sendMTF_numZ_mono eg znew znew znew znew znew znew znew) as S2.
  set (es := fst (sendMTFValues eg znew znew znew znew znew znew znew)) in *.
  rewrite G1 in S2. unfold est_set_bw in S2. cbn [e_bw] in S2.
  cps_destruct OK1 as (OA & OB & OC).
  pose proof (cb_trailer_numZ_mono b (e_bw es) (e_combinedCRC es)) as T1.
  set (h := cb_hdr e1) in *. set (bt := cb_trailer b (e_bw es) (e_combinedCRC es)) in *. set (bs := e_bw es) in *.
  clearbody es eg b1 e1 h bt bs. lia.
Qed.

Lemma cb_pos_last : forall e, e_nblock e <= 0 -> 0 <= bw_numZ (e_bw e) -> (e_blockNo e = 1 \/ bw_ok (e_bw e)) ->
  1 <= bw_numZ (e_bw (fst (compressBlock e true znew))).
Proof.
  intros e ZERO NZ BW. rewrite compressBlock_bw.
  replace (0 <? e_nblock e) with false by (symmetry; apply Z.ltb_ge; exact ZERO). cbv iota. unfold cb_trailer. cbv iota.
  set (e0 := est_set_bw e _).
  assert (OK0 : bw_ok (cb_hdr e0)).
  { apply hdr_ok; [subst e0; unfold est_set_bw; cbn [e_bw bw_numZ]; exact NZ|].
    subst e0; unfold est_set_bw; cbn [e_bw e_blockNo]. destruct BW as [BW|BW]; [left; exact BW| right].
    cps_destruct BW as (A & B & C). unfold bw_ok; cbn [bw_buff bw_live bw_numZ]. lia. }
  set (h := cb_hdr e0) in *.
  set (b1 := bsPutUInt32 _ (e_combinedCRC e)).
  assert (BB : bits b1 = bits h + 80) by (subst b1; unfold bsPutUInt32, bsPutUChar; rewrite !bsW_bits; lia).
  assert (OK1 : bw_ok b1) by (subst b1; apply bsPutUInt32_ok; do 6 apply bsPutUChar_ok_any; exact OK0).
  pose proof (bits_nonneg _ OK0) as B0. clearbody b1 h e0. cps_destruct OK1 as (OA & OB & OC).
  cps_destruct (finish_facts BS_FUEL b1) as (X1 & X2 & X3).
  pose proof (bs_finish_live BS_FUEL b1 ltac:(unfold BS_FUEL; change (8 * Z.of_nat 5)%Z with 40%Z; lia)) as LF.
  (* [comment removed for export] *)
  revert X1 X2 LF BB B0 OB OC. clear. generalize (bs_finish BS_FUEL b1) as bf. intros bf. unfold bits. intros. lia.
Qed.

Lemma cb_pos : forall e b, 0 <= bw_numZ (e_bw e) -> (e_blockNo e = 1 \/ bw_ok (e_bw e)) ->
  0 < e_nblock e \/ b = true -> 1 <= bw_numZ (e_bw (fst (compressBlock e b znew))).
Proof.
  intros e b NZ BW CASE. destruct (Z.lt_ge_cases 0 (e_nblock e)) as [POS|ZERO].
  - apply cb_pos_blk; assumption.
  - destruct CASE as [C|C]; [lia|]. subst b. apply cb_pos_last; [lia| assumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record CBE (cx : cctx) (g : eg) (e : est) (z : zstrm) : Prop := CE {
  ce_ok : est_ok e;
  ce_rl : rl_inv (est_rl e);
  ce_def : zdefr (e_inUse e) 0 256;
  ce_iu : inuse01 (e_inUse e);
  ce_mode : e_mode e = BZ_M_RUNNING \/ (e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = 0 /\ z_avail_in z = 0);
  ce_ain : z_avail_in z = Z.of_nat (length (z_in z));
  ce_inb : Forall (fun c => 0 <= c < 256) (z_in z);
  ce_aout : 0 <= z_avail_out z <= BZ_MAX_UNUSED /\ Z.of_nat (length (z_outr z)) = BZ_MAX_UNUSED - z_avail_out z;
  ce_tin : z_tin_hi z = 0 /\ 0 <= z_tin_lo z /\ z_tin_lo z + z_avail_in z < 67108864;
  ce_pot : 4 * e_nblock e + 5 * e_state_in_len e + 4 * NBLOCKMAX * (e_blockNo e - 1) <= 5 * z_tin_lo z;
  ce_st : e_state e = BZ_S_INPUT;
  ce_nz : bw_numZ (e_bw e) = 0;
  ce_pos : e_state_out_pos e = 0;
  ce_nb : e_nblock e <= NBLOCKMAX + 9;
  ce_bi : blk_iu (e_nblock e) (e_arr2 e) (e_inUse e);
  ce_bw : g_bs g = true -> bw_ok (e_bw e);
  ce_bs : e_blockNo e = 1 \/ g_bs g = true;
  ce_full : NBLOCKMAX <= e_nblock e \/ (e_mode e = BZ_M_FINISHING /\ isempty_RL (est_rl e) = true);
  ce_fin : e_mode e = BZ_M_FINISHING -> isempty_RL (est_rl e) = true
}.

(* [comment removed for export] *)

Section CB.
  Hypothesis M : cbm.

  (* [comment removed for export] *)
End CB.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section CBL.
  Hypothesis M : cbm.
  Variable CBF : est -> Prop.
  Hypothesis CBFI : forall g e, cb_pre g e -> cb_facts e -> CBF e.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End CBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hc_breaks_mono : forall f f' lj e z pin pout, hc_breaks f lj e z pin pout -> (f <= f')%nat -> hc_breaks f' lj e z pin pout.
Proof.
  induction f as [|f IH]; intros f' lj e z pin pout H L; [destruct H|].
  destruct f' as [|f']; [lia|]. rewrite hc_breaks_S in H |- *.
  destruct (hc_iter lj e z pin pout) as [[[[e1 z1] pin1] pout1] brk]. destruct brk; [exact I|]. apply (IH f'); [exact H| lia].
Qed.

(* [comment removed for export] *)

Section TERM.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End TERM.

Section TERM2.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End TERM2.

Section TERM3.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End TERM3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma law_cb_mode : forall e b, e_mode (fst (compressBlock e b znew)) = e_mode e.
Proof. intros e b. pose proof (cb_keep e b) as K. cbv zeta in K. exact (proj1 K). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PHI (e : est) (z : zstrm) : Z := 4 * e_nblock e + 5 * e_state_in_len e + 5 * z_avail_in z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma div_mono_4MAX : forall a b, 0 <= a <= b -> a / (4 * NBLOCKMAX) <= b / (4 * NBLOCKMAX).
Proof. intros a b H. apply Z.div_le_mono; [bz_params; lia| lia]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section BCB.
  Hypothesis M : cbm.
  (* [comment removed for export] *)
End BCB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BRK (e : est) (z : zstrm) : Prop :=
  (e_state e = BZ_S_OUTPUT /\ e_state_out_pos e < bw_numZ (e_bw e) /\ z_avail_out z = 0) \/
  (e_state e = BZ_S_OUTPUT /\ e_mode e = BZ_M_FINISHING /\ isempty_RL_e e = true /\ bw_numZ (e_bw e) <= e_state_out_pos e /\ e_avail_in_expect e = 0) \/
  (e_state e = BZ_S_INPUT /\ e_mode e = BZ_M_RUNNING /\ z_avail_in z = 0 /\ e_nblock e < NBLOCKMAX).
End ACeilS2.


(* [comment removed for export] *)
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CALL.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End CALL.

Section CALL2.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)
End CALL2.

Section CALL3.
  Hypothesis M : cbm.
  Variable cx : cctx.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End CALL3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BND (e : est) (z : zstrm) : Prop :=
  (e_state e = BZ_S_OUTPUT /\ e_state_out_pos e < bw_numZ (e_bw e)) \/
  (e_state e = BZ_S_INPUT /\ e_mode e = BZ_M_RUNNING /\ e_nblock e < NBLOCKMAX).
(* [comment removed for export] *)

(* [comment removed for export] *)

Section SESS.
  Hypothesis M : cbm.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End SESS.

Section SESS2.
  Hypothesis M : cbm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End SESS2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Section WSL.
  Hypothesis M : cbm.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End WSL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS3.
