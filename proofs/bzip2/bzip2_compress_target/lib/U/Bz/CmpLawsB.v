(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 BzCMtf BzCFactsGm. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpSess CmpSess2 CmpLaws CmpSessB BzRT1.
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
Record HCXB (cx : cctx) (on : Z) (g : eg) (e : est) (z : zstrm) : Prop := HXB {
  hx_ok : est_ok e;
  hx_rl : rl_inv (est_rl e);
  hx_def : zdefr (e_inUse e) 0 256;
  hx_iu : inuse01 (e_inUse e);
  hx_mode : e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = z_avail_in z;
  hx_ain : z_avail_in z = Z.of_nat (length (z_in z));
  hx_inb : Forall (fun c => 0 <= c < 256) (z_in z);
  hx_aout : 0 <= z_avail_out z <= on /\ Z.of_nat (length (z_outr z)) = on - z_avail_out z;
  hx_tin : z_tin_hi z = 0 /\ 0 <= z_tin_lo z /\ z_tin_lo z + z_avail_in z < 67108864;
  hx_pot : 4 * e_nblock e + 5 * e_state_in_len e + 4 * NBLOCKMAX * (e_blockNo e - 1) <= 5 * z_tin_lo z;
  hx_out : e_state e = BZ_S_OUTPUT ->
           g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) /\
           (forall k, 0 <= k < bw_numZ (e_bw e) -> zget (e_arr2 e) (e_nblock e + k) = zget (bw_zb (e_bw e)) k) /\
           (NBLOCKMAX <= e_nblock e \/ (e_avail_in_expect e = 0 /\ isempty_RL_e e = true)) /\ g_bs g = true;
  hx_numZ : e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE;
  hx_in : e_state e = BZ_S_INPUT ->
          bw_numZ (e_bw e) = 0 /\ e_state_out_pos e = 0 /\ e_nblock e <= NBLOCKMAX + 4 /\ blk_iu (e_nblock e) (e_arr2 e) (e_inUse e);
  (* [comment removed for export] *)
  hx_bw : g_bs g = true -> bw_ok (e_bw e) \/ (e_state e = BZ_S_OUTPUT /\ e_avail_in_expect e = 0 /\ isempty_RL_e e = true);
  hx_bs : e_blockNo e = 1 \/ g_bs g = true
}.

Lemma lawB_hci : forall cx on g e z, HCXB cx on g e z -> HCIB cx on g e z.
Proof.
  intros cx on g e z X. destruct X. unfold HCIB.
  split; [exact hx_ok0|]. split.
  { destruct hx_rl0 as [(A & B & C & D & E) P]. cbn [est_rl rl_nblock rl_crc rl_len rl_ch] in *.
    destruct (Z.ltb_spec (e_state_in_ch e) 256) as [L|L]; [right; split; [exact L| apply P; exact L]| left; lia]. }
  split; [exact hx_def0|]. split; [exact hx_mode0|]. split; [exact hx_ain0|]. split; [lia|]. split; [exact (proj1 hx_aout0)|].
  split; [exact (proj2 hx_aout0)|]. split; [| exact hx_numZ0].
  intros SO. cps_destruct (hx_out0 SO) as (G & K & _). split; [exact G|]. split; [exact hx_numZ0| exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lawB_co : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> z_avail_out z <> 0 ->
  e_state_out_pos e < bw_numZ (e_bw e) -> HCXB cx on g (fst (co_step e z)) (snd (co_step e z)).
Proof.
  intros cx on g e z X SO AO POS. rewrite co_step_eq. destruct X. unfold isempty_RL_e in *. split; cbn_acc; try assumption.
  - est_ok_from hx_ok0.
  - cbn [length]. lia.
  - intros SI. rewrite SI in SO. discriminate.
Qed.

Lemma lawB_ci : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT ->
  e_nblock e < NBLOCKMAX -> z_avail_in z <> 0 -> HCXB cx on g (fst (ci_stepF e z)) (snd (ci_stepF e z)).
Proof.
  intros cx on g e z X SI NB AI.
  destruct (z_in z) as [|c rest] eqn:ZIN.
  { exfalso. destruct X. rewrite ZIN in hx_ain0. cbn in hx_ain0. lia. }
  rewrite (ci_stepF_eq e z c rest ZIN). destruct X.
  cps_destruct (hx_in0 SI) as (NZ0 & POS0 & NB4 & BI). pose proof hx_ok0 as OK. unfold est_ok in OK.
  rewrite ZIN in hx_inb0. apply Forall_cons_iff in hx_inb0. destruct hx_inb0 as [Hc INB].
  assert (RX : RLX (est_rl e)) by (split; [exact hx_rl0| split; [unfold est_rl; cbn_acc; tauto| split; [exact hx_def0| split; [exact hx_iu0| exact BI]]]]).
  cps_destruct (add_char_RLX (est_rl e) c RX Hc) as ((INV' & BOK' & DEF' & U01' & BI') & NB' & POT' & _).
  unfold rl_pot in POT'. set (r' := add_char_to_block (est_rl e) c) in *.
  pose proof INV' as [(A' & B' & C' & D' & E') P'].
  assert (TL : m32 (z_tin_lo z + 1) = z_tin_lo z + 1) by (apply m32_small; lia).
  unfold z_adv. rewrite TL. replace (z_tin_lo z + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [est_rl rl_nblock rl_len rl_ch rl_crc rl_block rl_inUse] in *.
  rewrite ZIN in hx_ain0. cbn [length] in hx_ain0. cps_destruct hx_mode0 as (MF & GA & AIE).
  unfold isempty_RL_e in *. split; cbn_acc; try assumption; bz_params; try lia.
  all: try (est_ok_from hx_ok0).
  all: try (split; [exact MF|]; split; [exact GA|]; lia).
  all: try (intros SO; exfalso; rewrite SO in SI; discriminate).
  all: try (intros _; repeat apply conj; try lia; exact BI').
  intros BS. destruct (hx_bw0 BS) as [BW|[SO _]]; [left; exact BW| rewrite SI in SO; discriminate].
Qed.

Lemma lawB_prep_full : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT ->
  (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e = false -> NBLOCKMAX <= e_nblock e.
Proof.
  intros cx on g e z X SO STOP. cps_destruct (hx_out _ _ _ _ _ X SO) as (_ & _ & G3 & _).
  destruct G3 as [G3|[AIE EM]]; [exact G3|]. exfalso. cps_destruct (hx_mode _ _ _ _ _ X) as (M & _ & _).
  unfold isempty_RL_e in EM, STOP. rewrite M, AIE, EM in STOP. cbn in STOP. discriminate.
Qed.

Lemma lawB_prep : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> bw_numZ (e_bw e) <= e_state_out_pos e ->
  (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e = false ->
  HCXB cx on g (hc_prep e) z.
Proof.
  intros cx on g e z X SO DR STOP. pose proof (lawB_prep_full cx on g e z X SO STOP) as FULL. destruct X.
  cps_destruct (hx_out0 SO) as (G1 & G2 & G3 & G4).
  pose proof hx_ok0 as OK. unfold est_ok in OK.
  cps_destruct (prepare_RLX (est_rl e) hx_rl0 ltac:(unfold est_rl; cbn_acc; tauto)) as ((INV' & BOK' & DEF' & U01' & BI') & NB0 & L' & CH' & BLK' & CRC').
  unfold hc_prep, prepare_new_block. cbn_acc. rewrite NB0, L', CH', BLK', CRC' in *.
  set (iu' := rl_inUse (prepare_new_block_rl (est_rl e))) in *.
  pose proof crc_init_range as CIR. unfold isempty_RL_e in *.
  split; cbn_acc; try assumption; bz_params; try lia.
  all: try (est_ok_from hx_ok0).
  - intros SO'. exfalso. discriminate.
  - intros _. repeat apply conj; try lia. intros j Hj. lia.
  - intros BS. left. apply bw_ok_reset. destruct (hx_bw0 BS) as [BW|(_ & AIE & EM)]; [exact BW|]. exfalso.
    cps_destruct hx_mode0 as (M & _ & _). cbn_acc. rewrite M, AIE, EM in STOP. cbn in STOP. discriminate.
  - right. exact G4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record CBEB (cx : cctx) (on : Z) (g : eg) (e : est) (z : zstrm) : Prop := CEB {
  ce_ok : est_ok e;
  ce_rl : rl_inv (est_rl e);
  ce_def : zdefr (e_inUse e) 0 256;
  ce_iu : inuse01 (e_inUse e);
  ce_mode : e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = z_avail_in z;
  ce_ain : z_avail_in z = Z.of_nat (length (z_in z));
  ce_inb : Forall (fun c => 0 <= c < 256) (z_in z);
  ce_aout : 0 <= z_avail_out z <= on /\ Z.of_nat (length (z_outr z)) = on - z_avail_out z;
  ce_tin : z_tin_hi z = 0 /\ 0 <= z_tin_lo z /\ z_tin_lo z + z_avail_in z < 67108864;
  ce_pot : 4 * e_nblock e + 5 * e_state_in_len e + 4 * NBLOCKMAX * (e_blockNo e - 1) <= 5 * z_tin_lo z;
  ce_st : e_state e = BZ_S_INPUT;
  ce_nz : bw_numZ (e_bw e) = 0;
  ce_pos : e_state_out_pos e = 0;
  ce_nb : e_nblock e <= NBLOCKMAX + 9;
  ce_bi : blk_iu (e_nblock e) (e_arr2 e) (e_inUse e);
  ce_bw : g_bs g = true -> bw_ok (e_bw e);
  ce_bs : e_blockNo e = 1 \/ g_bs g = true;
  ce_full : NBLOCKMAX <= e_nblock e \/ (e_avail_in_expect e = 0 /\ isempty_RL (est_rl e) = true);
  ce_fin : e_avail_in_expect e = 0 -> isempty_RL (est_rl e) = true
}.

Lemma CBEB_entry : forall cx on g e z, CBEB cx on g e z -> cb_entry g e.
Proof.
  intros cx on g e z X. destruct X. pose proof ce_ok0 as OK. unfold est_ok in OK.
  split.
  - unfold cb_pre. split; [exact ce_ok0|]. split; [lia|]. split; [exact ce_def0|]. split; [unfold rd8; exact ce_bi0|].
    split; [lia|]. split; [intros _; exact ce_nz0|].
    destruct ce_bs0 as [B1|BS]; [left; exact B1| right]. split; [exact BS|]. split; [apply ce_bw0; exact BS| exact ce_nz0].
  - unfold cb_facts. split; [exact ce_pos0|]. split; [exact ce_nz0|]. split; [exact ce_rl0| exact ce_iu0].
Qed.

Section CB.
  Hypothesis M : cbm.

  Lemma CBEB_after : forall cx on g e z b, CBEB cx on g e z -> b = (e_avail_in_expect e =? 0) ->
    let e' := fst (compressBlock e b znew) in
    HCXB cx on (eg_after_cb cx g e) (est_set_modes e' (e_mode e') BZ_S_OUTPUT (e_avail_in_expect e')) z.
  Proof.
    intros cx on g e z b X Hb. pose proof (CBEB_entry cx on g e z X) as EN. destruct X. cbv zeta.
    pose proof ce_ok0 as OK. unfold est_ok in OK.
    pose proof (CmpLaws.cb_keep e b) as K. cbv zeta in K. cps_destruct K as (Kmode & Kst & Kaie & Knb & Kch & Klen & Kiu & Kbno & Kpos & Kcrc & Kcc & Ka2).
    cps_destruct (cbm_arrs M g e b EN) as (A1 & A2 & FT).
    pose proof (cb_zbits e b ltac:(lia)) as ZB. cbv zeta in ZB.
    assert (LV : 0 <= bw_live (e_bw e) <= 32 \/ e_blockNo e = 1).
    { destruct ce_bs0 as [B1|BS]; [right; exact B1| left]. cps_destruct (ce_bw0 BS) as (_ & L & _). exact L. }
    cps_destruct (compressBlock_numZ e b ltac:(lia) ltac:(lia) LV (cbm_gmf M g e EN)) as (N1 & N2 & N3).
    pose proof (cb_pos e b ltac:(lia) ltac:(destruct ce_bs0 as [B1|BS]; [left; exact B1| right; exact (ce_bw0 BS)])) as NP.
    set (e' := fst (compressBlock e b znew)) in *.
    assert (CR1 : 0 <= e_blockCRC e' < 4294967296).
    { rewrite Kcrc. destruct (0 <? e_nblock e); [apply crc_final_range|]; lia. }
    assert (CR2 : 0 <= e_combinedCRC e' < 4294967296).
    { rewrite Kcc. destruct (0 <? e_nblock e); [apply combinedCRC_e0_range|]; lia. }
    unfold eg_after_cb, isempty_RL_e, est_rl. split; cbn_acc; cbn [g_aie g_sort g_mtf g_bs g_zbits];
      rewrite ?Kmode, ?Kst, ?Kaie, ?Knb, ?Kch, ?Klen, ?Kiu, ?Kbno, ?Kpos; try assumption; bz_params; try lia.
    - (* [comment removed for export] *) unfold est_ok. cbn_acc.
      assert (NZ' : 0 <= bw_numZ (e_bw e')) by (destruct (0 <? e_nblock e); lia).
      repeat apply conj; try assumption; bz_params; try lia.
    - (* [comment removed for export] *) destruct ce_rl0 as [(R1 & R2 & R3 & R4 & R5) P]. unfold rl_inv, rl_ok in *. cbn_acc.
      repeat apply conj; try assumption; try lia.
    - (* [comment removed for export] *) intros _. split; [reflexivity|]. split; [exact ZB|]. split; [| reflexivity].
      destruct ce_full0 as [F|[Fm Fe]]; [left; exact F| right]. split; [exact Fm|]. cbn_acc. exact Fe.
    - intros SI. exfalso. discriminate.
    - intros _. destruct b; [right| left; exact (cbm_bw M g e EN)].
      symmetry in Hb. apply Z.eqb_eq in Hb. split; [reflexivity|]. split; [exact Hb|]. cbn_acc. exact (ce_fin0 Hb).
  Qed.
End CB.

Lemma CBEB_of_M : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e <> 0 -> NBLOCKMAX <= e_nblock e ->
  CBEB cx on g e z.
Proof.
  intros cx on g e z X SI NE FULL. destruct X. cps_destruct (hx_in0 SI) as (NZ & POS & NB4 & BI).
  split; try assumption; bz_params; try lia.
  all: try (intros BS; destruct (hx_bw0 BS) as [BW|[SO _]]; [exact BW| rewrite SI in SO; discriminate]).
  all: intros E0; exfalso; exact (NE E0).
Qed.

Lemma CBEB_of_F : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e = 0 ->
  CBEB cx on g (hc_flush e) z.
Proof.
  intros cx on g e z X SI E0. destruct X. cps_destruct (hx_in0 SI) as (NZ & POS & NB4 & BI).
  pose proof hx_ok0 as OK. unfold est_ok in OK.
  assert (RX : RLX (est_rl e)) by (split; [exact hx_rl0| split; [unfold est_rl; cbn; tauto| split; [exact hx_def0| split; [exact hx_iu0| exact BI]]]]).
  cps_destruct (flush_RLX (est_rl e) RX) as ((INV' & BOK' & DEF' & U01' & BI') & NB' & POT' & L0 & CH & EMP).
  unfold rl_pot in POT'. pose proof INV' as [(A' & B' & C' & D' & E') P'].
  revert INV' BOK' DEF' U01' BI' NB' POT' L0 CH EMP A' B' C' D' E' P'. unfold hc_flush. generalize (flush_RL (est_rl e)) as r. intros.
  cbn [est_rl rl_nblock rl_len rl_ch rl_block rl_inUse rl_crc] in *.
  split; cbn_acc; try assumption; bz_params; try lia.
  - est_ok_from hx_ok0.
  - intros BS. destruct (hx_bw0 BS) as [BW|[SO _]]; [exact BW| rewrite SI in SO; discriminate].
  - right. split; [exact E0| exact EMP].
  - intros _. exact EMP.
Qed.

Section CBL.
  Hypothesis M : cbm.
  Variable CBF : est -> Prop.
  Hypothesis CBFI : forall g e, cb_pre g e -> cb_facts e -> CBF e.

  Lemma lawB_cbM : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e <> 0 -> NBLOCKMAX <= e_nblock e ->
    cb_pre g e /\ CBF e /\ HCXB cx on (eg_after_cb cx g e) (hc_cbR e) z.
  Proof.
    intros cx on g e z X SI NE FULL. pose proof (CBEB_of_M cx on g e z X SI NE FULL) as CE0.
    destruct (CBEB_entry cx on g e z CE0) as [PRE FACTS].
    split; [exact PRE|]. split; [apply (CBFI g); assumption|].
    unfold hc_cbR. pose proof (CBEB_after M cx on g e z false CE0 ltac:(symmetry; apply Z.eqb_neq; exact NE)) as X'. cbv zeta in X'.
    destruct (compressBlock e false znew) as [e' loc]. exact X'.
  Qed.

  Lemma hc_flush_fields : forall e, e_mode (hc_flush e) = e_mode e /\ e_avail_in_expect (hc_flush e) = e_avail_in_expect e.
  Proof. intros e. unfold hc_flush. cbn_acc. split; reflexivity. Qed.

  Lemma lawB_cbF : forall cx on g e z, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> e_avail_in_expect e = 0 ->
    cb_pre g (hc_flush e) /\ CBF (hc_flush e) /\ HCXB cx on (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z.
  Proof.
    intros cx on g e z X SI E0. pose proof (CBEB_of_F cx on g e z X SI E0) as CE0.
    destruct (CBEB_entry cx on g (hc_flush e) z CE0) as [PRE FACTS].
    split; [exact PRE|]. split; [apply (CBFI g); assumption|].
    cps_destruct (hx_mode _ _ _ _ _ X) as (MF & _ & _). destruct (hc_flush_fields e) as [FM FA].
    unfold hc_cbF.
    replace (e_mode (hc_flush e) =? BZ_M_FINISHING) with (e_avail_in_expect (hc_flush e) =? 0)
      by (rewrite FM, FA, MF, E0; reflexivity).
    pose proof (CBEB_after M cx on g (hc_flush e) z _ CE0 eq_refl) as X'. cbv zeta in X'.
    destruct (compressBlock (hc_flush e) _ znew) as [e' loc]. exact X'.
  Qed.
End CBL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TERM.
  Hypothesis M : cbm.
  Variables (cx : cctx) (on : Z).

  Lemma PHI_nonneg : forall g e z, HCXB cx on g e z -> 0 <= PHI e z.
  Proof.
    intros g e z X. pose proof (hx_ok _ _ _ _ _ X) as OK. unfold est_ok in OK. pose proof (hx_ain _ _ _ _ _ X). unfold PHI. lia.
  Qed.

  Lemma co_runB : forall n g e z p, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> (Z.to_nat (z_avail_out z) < n)%nat ->
    let '(e', z', p') := copy_output n e z p in
    HCXB cx on g e' z' /\ e_state e' = BZ_S_OUTPUT /\
    (z_avail_out z' = 0 \/ bw_numZ (e_bw e') <= e_state_out_pos e') /\
    PHI e' z' = PHI e z /\
    (z_avail_out z = 0 -> e' = e).
  Proof.
    induction n as [|n IH]; intros g e z p X SO FU; [lia|].
    rewrite copy_output_S. pose proof (hx_aout _ _ _ _ _ X) as AO.
    destruct (Z.eqb_spec (z_avail_out z) 0) as [A0|A0].
    { cbv beta iota. repeat apply conj; try assumption; try lia; try (intros; reflexivity). }
    destruct (Z.leb_spec (bw_numZ (e_bw e)) (e_state_out_pos e)) as [DR|DR].
    { cbv beta iota. repeat apply conj; try assumption; try lia; try (intros; reflexivity). }
    pose proof (lawB_co cx on g e z X SO A0 DR) as X1. rewrite co_step_eq in X1 |- *. cbn [fst snd] in X1 |- *.
    specialize (IH g _ _ true X1). cbn_acc.
    specialize (IH SO ltac:(lia)).
    destruct (copy_output n _ _ true) as [[e' z'] p']. cps_destruct IH as (Y1 & Y2 & Y3 & Y4 & Y5).
    revert Y4. unfold PHI. cbn_acc. intros Y4. repeat apply conj; try assumption; try lia. all: intros; exfalso; lia.
  Qed.

  Lemma ci_runB : forall n g e z p, HCXB cx on g e z -> e_state e = BZ_S_INPUT -> (Z.to_nat (z_avail_in z) < n)%nat ->
    let '(e', z', p') := copy_input n e z p in
    HCXB cx on g e' z' /\ e_state e' = BZ_S_INPUT /\
    (NBLOCKMAX <= e_nblock e' \/ z_avail_in z' = 0) /\ z_avail_out z' = z_avail_out z /\ PHI e' z' <= PHI e z.
  Proof.
    induction n as [|n IH]; intros g e z p X SI FU; [lia|].
    rewrite (copy_input_S_fin n e z p). pose proof (hx_ain _ _ _ _ _ X) as AI. cps_destruct (hx_mode _ _ _ _ _ X) as (MF & GA & AIE).
    destruct (Z.leb_spec NBLOCKMAX (e_nblock e)) as [NB|NB].
    { cbv beta iota. repeat apply conj; try assumption; try reflexivity; try lia. }
    destruct (Z.eqb_spec (z_avail_in z) 0) as [A0|A0].
    { cbv beta iota. repeat apply conj; try assumption; try reflexivity; try lia. }
    rewrite MF. cbn [Z.eqb BZ_M_RUNNING BZ_M_FINISHING Pos.eqb].
    replace (e_avail_in_expect e =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    pose proof (lawB_ci cx on g e z X SI NB A0) as X1.
    destruct (z_in z) as [|c rest] eqn:ZIN; [cbn in AI; lia|].
    pose proof X as X0. destruct X0. cps_destruct (hx_in0 SI) as (_ & _ & _ & BI).
    rewrite ZIN in hx_inb0. apply Forall_cons_iff in hx_inb0. destruct hx_inb0 as [Hc _].
    assert (RX : RLX (est_rl e)) by (split; [exact hx_rl0| split; [pose proof hx_ok0 as OK; unfold est_ok in OK; unfold est_rl; cbn; tauto| split; [exact hx_def0| split; [exact hx_iu0| exact BI]]]]).
    cps_destruct (add_char_RLX (est_rl e) c RX Hc) as (_ & NB' & POT' & _). unfold rl_pot in POT'.
    rewrite (ci_stepF_eq e z c rest ZIN) in X1 |- *. cbv zeta in X1. cbv zeta. cbn [fst snd] in X1 |- *.
    specialize (IH g _ _ true X1). revert IH POT' NB'. unfold z_adv, PHI. generalize (add_char_to_block (est_rl e) c) as r. cbn_acc. intros r IH POT' NB'.
    specialize (IH SI ltac:(lia)). cbn [length] in AI.
    destruct (copy_input n _ _ true) as [[e' z'] p']. cps_destruct IH as (Y1 & Y2 & Y3 & Y4 & Y5).
    repeat apply conj; try assumption. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma in_runB : forall g e z pin pout, HCXB cx on g e z -> e_state e = BZ_S_INPUT ->
    let '(e1, z1, pin1, pout1, brk) := hc_in znew e z pin pout in
    brk = false /\ exists g1, HCXB cx on g1 e1 z1 /\ e_state e1 = BZ_S_OUTPUT /\ e_state_out_pos e1 < bw_numZ (e_bw e1) /\
    z_avail_out z1 = z_avail_out z /\ PHI e1 z1 <= PHI e z.
  Proof.
    intros g e z pin pout X SI. unfold hc_in.
    pose proof (ci_runB (Z.to_nat (z_avail_in z) + 1) g e z pin X SI ltac:(lia)) as CI.
    destruct (copy_input _ e z pin) as [[e' z'] p']. cps_destruct CI as (X' & SI' & STOP & AO' & PH').
    cps_destruct (hx_mode _ _ _ _ _ X') as (MF' & GA' & AIE').
    rewrite MF'. cbn [Z.eqb BZ_M_RUNNING BZ_M_FINISHING Pos.eqb negb andb].
    destruct (Z.eqb_spec (e_avail_in_expect e') 0) as [E0|NE].
    - (* [comment removed for export] *)
      pose proof (CBEB_of_F cx on g e' z' X' SI' E0) as CE0.
      change (est_set_rl e' (flush_RL (est_rl e'))) with (hc_flush e').
      assert (HB : true = (e_avail_in_expect (hc_flush e') =? 0)) by (unfold hc_flush; cbn_acc; rewrite E0; reflexivity).
      pose proof (CBEB_after M cx on g (hc_flush e') z' true CE0 HB) as X1. cbv zeta in X1.
      pose proof (cb_pos (hc_flush e') true ltac:(rewrite (ce_nz _ _ _ _ _ CE0); lia)
                    ltac:(destruct (ce_bs _ _ _ _ _ CE0) as [B1|BS]; [left; exact B1| right; exact (ce_bw _ _ _ _ _ CE0 BS)])
                    ltac:(right; reflexivity)) as NP.
      pose proof (CmpLaws.cb_keep (hc_flush e') true) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & Knb & _ & Klen & _ & _ & Kpos & _).
      assert (PHF : PHI (hc_flush e') z' <= PHI e' z').
      { pose proof X' as X0. destruct X0. cps_destruct (hx_in0 SI') as (_ & _ & _ & BI).
        assert (RX : RLX (est_rl e')) by (split; [exact hx_rl0| split; [pose proof hx_ok0 as OK; unfold est_ok in OK; unfold est_rl; cbn; tauto| split; [exact hx_def0| split; [exact hx_iu0| exact BI]]]]).
        cps_destruct (flush_RLX (est_rl e') RX) as (_ & NB' & POT' & _). unfold rl_pot in POT'.
        revert NB' POT'. unfold PHI, hc_flush. generalize (flush_RL (est_rl e')) as r. cbn_acc. intros. lia. }
      replace (e_mode (hc_flush e') =? BZ_M_FINISHING) with true by (unfold hc_flush; cbn_acc; rewrite MF'; reflexivity).
      destruct (compressBlock (hc_flush e') true znew) as [e2 loc]. cbn [fst] in *.
      split; [reflexivity|]. exists (eg_after_cb cx g (hc_flush e')). split; [exact X1|]. cbn_acc. split; [reflexivity|].
      split; [rewrite Kpos, (ce_pos _ _ _ _ _ CE0); lia|]. split; [exact AO'|].
      revert PHF PH'. unfold PHI. cbn_acc. rewrite Knb, Klen. intros. lia.
    - destruct (Z.leb_spec NBLOCKMAX (e_nblock e')) as [FULL|NF].
      + pose proof (CBEB_of_M cx on g e' z' X' SI' NE FULL) as CE0.
        pose proof (CBEB_after M cx on g e' z' false CE0 ltac:(symmetry; apply Z.eqb_neq; exact NE)) as X1. cbv zeta in X1.
        pose proof (CBEB_entry _ _ _ _ _ CE0) as [PRE FACTS].
        pose proof (cb_pos e' false ltac:(rewrite (ce_nz _ _ _ _ _ CE0); lia)
                      ltac:(destruct (ce_bs _ _ _ _ _ CE0) as [B1|BS]; [left; exact B1| right; exact (ce_bw _ _ _ _ _ CE0 BS)])
                      ltac:(left; bz_params; lia)) as NP.
        pose proof (CmpLaws.cb_keep e' false) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & Knb & _ & Klen & _ & _ & Kpos & _).
        destruct (compressBlock e' false znew) as [e2 loc]. cbn [fst] in *.
        split; [reflexivity|]. exists (eg_after_cb cx g e'). split; [exact X1|]. cbn_acc. split; [reflexivity|].
        split; [rewrite Kpos, (ce_pos _ _ _ _ _ CE0); lia|]. split; [exact AO'|].
        revert PH'. unfold PHI. cbn_acc. rewrite Knb, Klen. intros. lia.
      + exfalso. destruct STOP as [F|A0]; [lia|]. rewrite AIE' in NE. exact (NE A0).
  Qed.

  (* [comment removed for export] *)
  Lemma iter_runB : forall g e z pin pout, HCXB cx on g e z ->
    let '(e1, z1, pin1, pout1, brk) := hc_iter znew e z pin pout in
    brk = false -> exists g1, HCXB cx on g1 e1 z1 /\ e_state e1 = BZ_S_OUTPUT /\ e_state_out_pos e1 < bw_numZ (e_bw e1) /\
      PHI e1 z1 <= PHI e z /\
      (e_state e = BZ_S_OUTPUT -> PHI e1 z1 + 4 * NBLOCKMAX <= PHI e z).
  Proof.
    intros g e z pin pout X.
    pose proof (hx_ok _ _ _ _ _ X) as OK. unfold est_ok in OK.
    assert (ST : e_state e = BZ_S_OUTPUT \/ e_state e = BZ_S_INPUT) by tauto.
    destruct ST as [SO|SI].
    - rewrite (CmpSess.hc_iter_output znew e z pin pout SO). unfold hc_out.
      pose proof (co_runB (Z.to_nat (z_avail_out z) + 1) g e z pout X SO ltac:(lia)) as CO.
      destruct (copy_output _ e z pout) as [[e' z'] p']. cps_destruct CO as (X' & SO' & DR & PH & ID).
      destruct (Z.ltb_spec (e_state_out_pos e') (bw_numZ (e_bw e'))) as [P|P]; [intros; discriminate|].
      destruct ((e_mode e' =? BZ_M_FINISHING) && (e_avail_in_expect e' =? 0) && isempty_RL_e e') eqn:STOP; [intros; discriminate|].
      pose proof (lawB_prep cx on g e' z' X' SO' ltac:(lia) STOP) as XP.
      pose proof (lawB_prep_full cx on g e' z' X' SO' STOP) as FULL.
      assert (NOFL : (e_mode (hc_prep e') =? BZ_M_FLUSHING) && (e_avail_in_expect (hc_prep e') =? 0) && isempty_RL_e (hc_prep e') = false).
      { destruct (hx_mode _ _ _ _ _ XP) as (MF & _). rewrite MF. reflexivity. }
      rewrite NOFL.
      assert (SI1 : e_state (hc_prep e') = BZ_S_INPUT) by reflexivity.
      assert (PHP : PHI (hc_prep e') z' + 4 * e_nblock e' = PHI e' z').
      { unfold PHI, hc_prep, prepare_new_block, prepare_new_block_rl. cbn_acc. lia. }
      pose proof (in_runB g (hc_prep e') z' pin p' XP SI1) as IR.
      destruct (hc_in znew (hc_prep e') z' pin p') as [[[[e1 z1] pin1] pout1] brk]. intros B.
      cps_destruct IR as (_ & g1 & X1 & SO1 & P1 & AO1 & PH1). exists g1. split; [exact X1|]. split; [exact SO1|]. split; [exact P1|].
      bz_params. split; [lia|]. intros _. lia.
    - rewrite (CmpSess.hc_iter_input znew e z pin pout SI).
      pose proof (in_runB g e z pin pout X SI) as IR.
      destruct (hc_in znew e z pin pout) as [[[[e1 z1] pin1] pout1] brk]. intros B.
      cps_destruct IR as (_ & g1 & X1 & SO1 & P1 & AO1 & PH1). exists g1. repeat apply conj; try assumption.
      intros SO. rewrite SI in SO. discriminate.
  Qed.

  Lemma div_4MAX_step : forall a b, 0 <= a -> a + 4 * NBLOCKMAX <= b -> a / (4 * NBLOCKMAX) + 1 <= b / (4 * NBLOCKMAX).
  Proof.
    intros a b Ha H. bz_params.
    replace (a / (4 * NBLOCKMAX) + 1) with ((a + 1 * (4 * NBLOCKMAX)) / (4 * NBLOCKMAX)) by (rewrite Z.div_add by lia; reflexivity).
    apply Z.div_le_mono; lia.
  Qed.

  Lemma breaks_outB : forall k g e z pin pout, HCXB cx on g e z -> e_state e = BZ_S_OUTPUT -> e_state_out_pos e < bw_numZ (e_bw e) ->
    PHI e z / (4 * NBLOCKMAX) < Z.of_nat k -> hc_breaks (S k) znew e z pin pout.
  Proof.
    induction k as [|k IH]; intros g e z pin pout X SO PEND FU.
    - exfalso. pose proof (PHI_nonneg g e z X). pose proof (Z.div_pos (PHI e z) (4 * NBLOCKMAX)). bz_params. cbn in FU. lia.
    - rewrite hc_breaks_S. pose proof (iter_runB g e z pin pout X) as IR.
      destruct (hc_iter znew e z pin pout) as [[[[e1 z1] pin1] pout1] brk]. destruct brk; [exact I|].
      cps_destruct (IR eq_refl) as (g1 & X1 & SO1 & P1 & _ & DROP). specialize (DROP SO).
      apply (IH g1); try assumption.
      pose proof (div_4MAX_step (PHI e1 z1) (PHI e z) (PHI_nonneg g1 e1 z1 X1) DROP). lia.
  Qed.

  Lemma lawB_term : forall g e z, HCXB cx on g e z -> hc_breaks (hc_fuel z) znew e z false false.
  Proof.
    intros g e z X.
    pose proof (hx_ok _ _ _ _ _ X) as OK. unfold est_ok in OK. pose proof (hx_ain _ _ _ _ _ X) as AI. pose proof (hx_tin _ _ _ _ _ X) as TI.
    assert (PB : PHI e z / (4 * NBLOCKMAX) < 841).
    { apply Z.div_lt_upper_bound; [bz_params; lia|]. unfold PHI. bz_params. lia. }
    pose proof (Z.div_pos (PHI e z) (4 * NBLOCKMAX) (PHI_nonneg g e z X) ltac:(bz_params; lia)) as P0.
    set (K := (Z.to_nat (PHI e z / (4 * NBLOCKMAX)) + 1)%nat).
    apply (hc_breaks_mono (S (S K))).
    - rewrite hc_breaks_S. pose proof (iter_runB g e z false false X) as IR.
      destruct (hc_iter znew e z false false) as [[[[e1 z1] pin1] pout1] brk]. destruct brk; [exact I|].
      cps_destruct (IR eq_refl) as (g1 & X1 & SO1 & P1 & LE & _).
      apply (breaks_outB K g1); try assumption.
      pose proof (div_mono_4MAX (PHI e1 z1) (PHI e z) (conj (PHI_nonneg g1 e1 z1 X1) LE)). subst K. lia.
    - unfold hc_fuel. subst K. pose proof (Z.div_pos (z_avail_in z) NBLOCKMAX ltac:(lia) ltac:(bz_params; lia)). unfold BZ_MAX_UNUSED. lia.
  Qed.
End TERM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem hc_lawsB_intro : cbm -> forall CBF : est -> Prop, (forall g e, cb_pre g e -> cb_facts e -> CBF e) -> hc_lawsB HCXB CBF.
Proof.
  intros M CBF CBFI. split.
  - exact lawB_hci.
  - exact lawB_co.
  - exact lawB_ci.
  - exact lawB_prep.
  - exact (lawB_cbM M CBF CBFI).
  - exact (lawB_cbF M CBF CBFI).
  - intros cx on g e z X. exact (lawB_term M cx on g e z X).
  - exact law_cb_mode.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma HCXB_init : forall cx on zb (pl : list Z) a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM,
  zbok a1 -> zbok a2 -> (forall i, 0 <= zget ft i < 4294967296) ->
  0 <= on -> Z.of_nat (length pl) < 67108864 -> Forall (fun c => 0 <= c < 256) pl ->
  let e0 := est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM in
  let z := z_b2b pl on in
  HCXB cx on (eg_set_aie (eg_init zb)) (e_finish e0 z) z.
Proof.
  intros cx on zb pl a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM Z1 Z2 FT ON LEN BY. cbv zeta.
  pose proof crc_init_range as CR.
  assert (IU0 : forall j, 0 <= j < 256 -> zget (inUse_clear inU 0 256) j = 0).
  { intros j Hj. apply inUse_clear_zero. cbn. lia. }
  unfold est_init, z_b2b, e_finish, eg_set_aie, eg_init. split; cbn_acc; cbn [g_aie g_bs g_zbits g_sort g_mtf length]; try lia.
  all: try exact BY.
  all: try (intros D; discriminate).
  all: try apply inUse_clear_zdefr.
  all: try (intros i Hi; left; apply IU0; exact Hi).
  all: try (repeat split; reflexivity).
  all: try (intros _; repeat apply conj; try lia; intros j Hj; lia).
  all: try (unfold rl_inv, rl_ok; cbn_acc; lia).
  unfold est_ok. cbn_acc. repeat apply conj; try assumption; try lia.
  all: bz_params; lia.
Qed.

End ACeilS1.
