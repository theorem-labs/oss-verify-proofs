(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmas1 BzCLemmasFs BzCRebuildF BzCPermF BzCFactsGm BzCSmF1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortPost. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCEmit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpSess.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory BzR3aFs BzR2D1 BzR2D. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzR2E BzR2Eb.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5a.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS BzR4a BzR4d.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4x.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.BzR5cX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4d OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.BzR4e OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4x.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR1a BzR1e.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR1b.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR1b. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzRT1 BzRT2.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1e OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1b.BzR1d OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1b OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzRT1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzRT2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzRTD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRTB1 BzRTB2.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma set_sv_fields : forall x v,
  d_state (d_set_sv x v) = d_state x /\ d_small (d_set_sv x v) = d_small x /\ d_rand (d_set_sv x v) = d_rand x /\
  d_bs100k (d_set_sv x v) = d_bs100k x /\ d_tt (d_set_sv x v) = d_tt x /\ d_cftab (d_set_sv x v) = d_cftab x /\
  d_ll16 (d_set_sv x v) = d_ll16 x /\ d_ll4 (d_set_sv x v) = d_ll4 x /\ d_sv (d_set_sv x v) = v /\
  d_nused (d_set_sv x v) = d_nused x /\ d_k0 (d_set_sv x v) = d_k0 x /\ d_tPos (d_set_sv x v) = d_tPos x /\
  d_out_len (d_set_sv x v) = d_out_len x /\ d_cbcrc (d_set_sv x v) = d_cbcrc x /\ d_sbcrc (d_set_sv x v) = d_sbcrc x /\
  d_cccrc (d_set_sv x v) = d_cccrc x.
Proof. intros x v. repeat split; reflexivity. Qed.

Lemma gp_maps_eq : forall x, mk_maps 256 (e_inUse x) (e_unseqToSeq x) 0 0 = (gp_unseq x, gp_nInUse x).
Proof. intros x. rewrite gp_unseq_eq, gp_nInUse_eq. destruct (mk_maps 256 (e_inUse x) (e_unseqToSeq x) 0 0); reflexivity. Qed.

(* [comment removed for export] *)
Lemma dec_ws_flat : forall crc op inUse in160 sel selMtf0 pos0 len nG nS us nI,
  dec_ws crc op inUse in160 sel selMtf0 pos0 len nG nS us nI =
  ws_blk_hdr crc op ++ ws_bits16 16 (fun i => bit01 (zget (sm_in16 16 in160 inUse 0) i)) 0 ++
  ws_rows 16 (fun i => bit01 (zget (sm_in16 16 in160 inUse 0) i)) (fun c => bit01 (zget inUse c)) 0 ++ [(3, nG); (15, nS)] ++
  ws_unary (Z.to_nat nS) (fun j => zget (snd (sm_selmtf (Z.to_nat nS) (yy_init (Z.to_nat nG) pos0 0) sel selMtf0 0)) j) 0 ++
  ws_dtables (Z.to_nat nG) (fun t0 v => zget len (258 * t0 + v)) (Z.to_nat (nI + 2)) 0 ++
  ws_sym (fun g => zget sel g) (fun t0 => Lrow len (258 * t0)) (nI + 2) 0 (genc nI (nI + 1) (fun k => k) 0 us).
Proof.
  intros. unfold dec_ws, hdr_ws. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma dec_block_v : forall t pi rho, bwt t pi rho ->
  forall crc op inUse in160 unseq0 sel selMtf0 pos0 len nG nS us unseq nI,
  mk_maps 256 inUse unseq0 0 0 = (unseq, nI) ->
  0 <= crc < 4294967296 -> op = Z.of_nat (origPtr rho) ->
  (forall b, In b t -> zget inUse b = 1) ->
  2 <= nG <= 6 -> 1 <= nS <= 18001 ->
  (forall k, 0 <= k < nS -> 0 <= zget sel k < nG) ->
  (forall t0 v, 0 <= t0 < nG -> 0 <= v < nI + 2 -> 1 <= zget len (258 * t0 + v) <= 20) ->
  (forall t0 k, 0 <= t0 < nG -> 1 <= k -> wsum (Lrow len (258 * t0)) (nI + 2) k <= 2 ^ k) ->
  length us = length t ->
  (forall i, (i < length t)%nat -> nth i us 0 = zget unseq (Lc t pi i)) ->
  Z.of_nat (length (genc nI (nI + 1) (fun k => k) 0 us)) <= 50 * nS ->
  Z.of_nat (length t) < 2 ^ 20 ->
  forall L d s rest, rd_ok d s -> bits_ok rest ->
  rd_abs d s = bapp (wbits (ws_blk_hdr crc op ++ ws_bits16 16 (fun i => bit01 (zget (sm_in16 16 in160 inUse 0) i)) 0 ++
     ws_rows 16 (fun i => bit01 (zget (sm_in16 16 in160 inUse 0) i)) (fun c => bit01 (zget inUse c)) 0 ++ [(3, nG); (15, nS)] ++
     ws_unary (Z.to_nat nS) (fun j => zget (snd (sm_selmtf (Z.to_nat nS) (yy_init (Z.to_nat nG) pos0 0) sel selMtf0 0)) j) 0 ++
     ws_dtables (Z.to_nat nG) (fun t0 v => zget len (258 * t0 + v)) (Z.to_nat (nI + 2)) 0 ++
     ws_sym (fun g => zget sel g) (fun t0 => Lrow len (258 * t0)) (nI + 2) 0 (genc nI (nI + 1) (fun k => k) 0 us))) rest ->
  Z.of_nat (length t) <= 100000 * d_bs100k d ->
  exists k L' d' s1 kb cf cc tt l16 l4,
    let dX := bend_upd t pi rho (smallb d) d' cf cc tt l16 l4 in
    (forall f, drun (k + f) 14 L d s = dgo f (DRet BZ_OK (bend_L t pi rho (smallb d) L') dX s1)) /\
    Z.of_nat k <= dcost d s dX s1 /\ consumed_from kb s s1 /\
    rd_abs dX s1 = rest /\ rd_ok dX s1 /\ TV t pi rho (smallb d) dX /\ sv_nblock L' = Z.of_nat (length t) /\
    d_sbcrc d' = crc /\ d_cccrc d' = d_cccrc d /\ d_bs100k d' = d_bs100k d /\ d_small d' = d_small d /\ d_blockNo d' = d_blockNo d + 1.
Proof.
  intros t pi rho HB crc op inUse in160 unseq0 sel selMtf0 pos0 len nG nS us unseq nI HM H1 H2 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
         L d s rest RD BO AB CAP.
  rewrite <- dec_ws_flat in AB.
  exact (dec_block t pi rho HB crc op inUse in160 unseq0 sel selMtf0 pos0 len nG nS us unseq nI HM H1 H2 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
           L d s rest RD BO AB CAP).
Qed.

Section BZPS. Context {BZP : BzParams}.

(* [comment removed for export] *)
Notation EB_e1 e := (cb_sorted e) (only parsing).
Notation EB_e1g e := (est_set_bw (cb_sorted e) (cb_bhdr (cb_hdr (cb_sorted e)) (cb_sorted e))) (only parsing).
Notation EB_eg e := (fst (generateMTFValues (EB_e1g e) znew)) (only parsing).
Notation EB_nI e := (e_nInUse (EB_eg e)) (only parsing).
Notation EB_A e := (e_nInUse (EB_eg e) + 2) (only parsing).
Notation EB_nMTF e := (e_nMTF (EB_eg e)) (only parsing).
Notation EB_nG e := (sm_nGroups (e_nMTF (EB_eg e))) (only parsing).
Notation EB_it e :=
  (sm_iters BZ_N_ITERS (e_arr1 (EB_eg e)) (EB_nG e) (EB_A e) (EB_nMTF e)
    (SITS (ip_len (sm_init_tables 8 (e_mtfFreq (EB_eg e)) (EB_nG e) (EB_A e) (SIP (sm_len_init 6 (e_len (EB_eg e)) (EB_A e) 0) (EB_nG e) (EB_nMTF e) 0)))
          (e_rfreq (EB_eg e)) (e_len_pack (EB_eg e)) (e_selector (EB_eg e)) znew znew 0 znew znew znew)) (only parsing).
Notation EB_nS e := (it_nSel (EB_it e)) (only parsing).
Notation EB_selMtf e := (snd (sm_selmtf (Z.to_nat (EB_nS e)) (yy_init (Z.to_nat (EB_nG e)) znew 0) (it_sel (EB_it e)) (e_selectorMtf (EB_eg e)) 0)) (only parsing).
Notation EB_code e := (sm_assign (Z.to_nat (EB_nG e)) (e_code (EB_eg e)) (it_len (EB_it e)) (EB_A e) 0) (only parsing).
Notation EB_in16 e := (sm_in16 16 znew (e_inUse (EB_eg e)) 0) (only parsing).

(* [comment removed for export] *)
Lemma BODY_ok : forall e, EB e -> 0 < e_nblock e ->
  let e1 := cb_sorted e in
  let eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew) in
  e_bw (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = wapp (cb_bhdr (cb_hdr e1) e1) (body_ws e) /\ wlegal (body_ws e).
Proof. intros e HE _. cbv zeta. split; [exact (eb_body e HE)| exact (eb_legal e HE)]. Qed.
Lemma ORIG_ok : forall e, EB e -> 0 < e_nblock e -> 0 <= e_origPtr (cb_sorted e) < 2 ^ 24.
Proof. intros e HE _. exact (eb_orig e HE). Qed.

Section SM.
  Variable sm : bool.

  (* [comment removed for export] *)
  Definition READY (e : est) (dfin : dst) : Prop :=
    let t := rl_bytes (est_rl e) in
    exists pi rho, bwt t pi rho /\ TV t pi rho sm dfin /\ sv_nblock (d_sv dfin) = Z.of_nat (length t) /\
      d_nused dfin = 1 /\ d_k0 dfin = sym t pi rho sm 0 /\ d_tPos dfin = pos t pi rho sm 1 /\ d_out_len dfin = 0 /\ d_cbcrc dfin = crc_init.

  Theorem BLK_UNRLE_ok : forall e dfin s,
    EB e -> 0 < e_nblock e -> READY e dfin -> Z.of_nat (length (rl_data (est_rl e))) <= s_avail_out s ->
    let seg := rl_data (est_rl e) in let len := Z.of_nat (length seg) in
    exists d'', unRLE dfin s = (0, d'', DSTRM (s_in s) (rev seg ++ s_out s) (s_avail_out s - len) (s_tin s) (s_tout s + len)) /\
      d_nused d'' = sv_nblock (d_sv dfin) + 1 /\ d_out_len d'' = 0 /\ d_cbcrc d'' = e_blockCRC e /\
      d_sv d'' = d_sv dfin /\ d_state d'' = d_state dfin /\ d_sbcrc d'' = d_sbcrc dfin /\ d_cccrc d'' = d_cccrc dfin /\
      d_bsBuff d'' = d_bsBuff dfin /\ d_bsLive d'' = d_bsLive dfin /\ d_bs100k d'' = d_bs100k dfin /\ d_small d'' = d_small dfin.
  Proof.
    (intros e dfin s HE NBP; cps_intros (pi & rho & BW & TVd & SV & N1 & K0 & TP & OL & CB); intros AV). cbv zeta.
    cps_destruct HE as (_ & _ & _ & _ & _ & RL). cps_pose (RLI_facts _ RL) as (RC & CRC & _).
    cps_destruct (unRLE_block _ pi rho BW sm dfin s (rl_data (est_rl e)) TVd SV N1 K0 TP OL RC AV) as (d'' & U & F1 & F2 & F3 & G).
    cps_destruct G as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G20 & G21 & G22 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G36).
    exists d''. split; [exact U|]. split; [exact F1|]. split; [exact F2|]. split; [rewrite F3, CB; symmetry; exact CRC|].
    split; [exact G36|]. split; [exact G1|]. split; [exact G20|]. split; [exact G22|]. split; [exact G5|]. split; [exact G6|]. split; [exact G7| exact G8].
  Qed.

  (* [comment removed for export] *)
  Lemma eb_gsyms : forall e, EB e -> gsyms (EB_e1g e) = genc (EB_nI e) (EB_nI e + 1) (fun k => k) 0 (us e).
  Proof.
    intros e HE. pose proof (eb_syms e HE) as S. cbv zeta in S. cps_destruct S as (_ & _ & _ & _ & _ & _ & X7 & NIE & _).
    pose proof (e1g_fields e HE) as (GNB & _).
    unfold gsyms. rewrite X7, NIE, GNB. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem BLK_DEC_ok : forall e L d s rest,
    EB e -> 0 < e_nblock e -> DINV sm d -> rd_ok d s -> bits_ok rest ->
    rd_abs d s = bapp (wbits (ws_bhdr_e (crc_final (e_blockCRC e)) (e_origPtr (cb_sorted e)) ++ body_ws e)) rest ->
    exists k L' d' s1 kb, let dfin := d_set_sv d' L' in
      (forall f, drun (k + f) 14 L d s = dgo f (DRet BZ_OK L' d' s1)) /\ Z.of_nat k <= dcost d s d' s1 /\ consumed_from kb s s1 /\
      rd_abs d' s1 = rest /\ rd_ok d' s1 /\
      d_state dfin = BZ_X_OUTPUT /\ sv_nblock L' = e_nblock e /\ DINV sm dfin /\
      d_sbcrc dfin = crc_final (e_blockCRC e) /\ d_cccrc dfin = d_cccrc d /\
      READY e dfin.
  Proof.
    intros e L d s rest HE NBP [DB DS] RD BO AB.
    cps_pose (e1_sort e HE) as (_ & _ & _ & _ & _ & _ & _ & _ & BW & _).
    cps_pose (eb_misc e HE) as (CR & EO & IU & COV & LT & L20 & LBS & GIE & GIU & X4 & X3 & RC & CRC & ET).
    pose proof (eb_tables e HE) as T; cbv zeta in T; cps_destruct T as (NS & KB & SEL & RO & KR & CC & SMT).
    cps_pose (eb_ranges e HE) as (RI & RA & RM & RG & MV).
    pose proof (eb_syms e HE) as S; cbv zeta in S; cps_destruct S as (LUS & LX & ML & _ & _ & FUS & EOB1 & NIE & L50).
    pose proof (eb_nb e HE) as NBR.
    rewrite (eb_gsyms e HE) in L50.
    assert (HM : mk_maps 256 (e_inUse e) (e_unseqToSeq (EB_e1g e)) 0 0 = (gp_unseq (EB_e1g e), EB_nI e)).
    { pose proof (gp_maps_eq (EB_e1g e)) as M. rewrite GIU in M. rewrite M, NIE. reflexivity. }
    assert (CAP : Z.of_nat (length (t e)) <= 100000 * d_bs100k d) by (rewrite DB; lia).
    assert (USL : length (us e) = length (t e)) by (rewrite LUS, LT; reflexivity).
    assert (USN : forall i, (i < length (t e))%nat -> nth i (us e) 0 = zget (gp_unseq (EB_e1g e)) (Lc (t e) (pi e) i)).
    { intros i Hi. apply (us_nth e HE). rewrite <- LT. exact Hi. }
    pose proof (eb_exchange e HE) as EX. cbv zeta in EX. rewrite (eb_gsyms e HE) in EX. rewrite EX in AB. clear EX.
    cps_destruct (dec_block_v (t e) (pi e) (rho e) BW (crc_final (e_blockCRC e)) (e_origPtr (EB_e1 e)) (e_inUse e) znew (e_unseqToSeq (EB_e1g e))
                (it_sel (EB_it e)) (e_selectorMtf (EB_eg e)) znew (it_len (EB_it e)) (EB_nG e) (EB_nS e) (us e) (gp_unseq (EB_e1g e)) (EB_nI e)
                HM CR EO COV RG NS SEL (eb_it_len20 e HE) KR USL USN L50 L20 L d s rest RD BO AB CAP)
      as (k & L' & d' & s1 & kb & cf & cc & tt & l16 & l4 & X). cbv zeta in X.
    cps_destruct X as (RUN & CO & CF & AB2 & RD2 & TVX & SVN & SB & CC2 & BS2 & SM2 & BN2).
    match type of TVX with TV _ _ _ _ ?x => set (dX := x) in * end.
    exists k, (bend_L (t e) (pi e) (rho e) (smallb d) L'), dX, s1, kb. cbv zeta.
    cps_pose (set_sv_fields dX (bend_L (t e) (pi e) (rho e) (smallb d) L')) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (bend_upd_fields (t e) (pi e) (rho e) (smallb d) d' cf cc tt l16 l4) as U. cbv zeta in U. fold dX in U.
    cps_destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & _ & _ & _ & _ & _ & U13 & U14 & U15 & _ & U17 & _ & U19 & _).
    pose proof (bend_L_fields (t e) (pi e) (rho e) (smallb d) L') as (BL1 & _).
    split; [exact RUN|]. split; [exact CO|]. split; [exact CF|]. split; [exact AB2|]. split; [exact RD2|].
    split; [rewrite F1; exact U1|]. split; [rewrite BL1, SVN, LT; lia|].
    split. { split; [rewrite F4, U15, BS2; exact DB| unfold smallb at 1; rewrite F2, U13, SM2; exact DS]. }
    split; [rewrite F15, U17; exact SB|]. split; [rewrite F16, U19; exact CC2|].
    unfold READY. rewrite <- ET. exists (pi e), (rho e). split; [exact BW|].
    split. { apply (TV_frame (t e) (pi e) (rho e) sm dX); [rewrite <- DS; exact TVX| exact F2| exact F3| exact F4| exact F5| exact F6| exact F7| exact F8]. }
    split; [rewrite F9, BL1; exact SVN|]. split; [rewrite F10; exact U7|]. split; [rewrite F11, U5, DS; reflexivity|].
    split; [rewrite F12, U6, DS; reflexivity|]. split; [rewrite F13; exact U2| rewrite F14; exact U4].
  Qed.

  (* [comment removed for export] *)
  Theorem rt_core : forall junk e0 payload dl,
    E0OK' e0 -> SI (e_fin e0 (Z.of_nat (length payload))) -> bytes payload -> Z.of_nat (length payload) <= dl ->
    let '(r, n, out, _) := buffToBuffDecompress junk (enc_stream e0 payload) dl (if sm then 1 else 0) in
    (r, n, out) = (BZ_OK, Z.of_nat (length payload), payload).
  Proof.
    exact (b2b_roundtrip_junk EB body_ws BODY_ok ORIG_ok SI SI_rl SI_entry READY sm BLK_DEC_ok BLK_UNRLE_ok EB_crc SI_cc).
  Qed.
End SM.

(* [comment removed for export] *)
Theorem rt_small : forall small junk e0 payload dl, small = 0 \/ small = 1 ->
  E0OK' e0 -> SI (e_fin e0 (Z.of_nat (length payload))) -> bytes payload -> Z.of_nat (length payload) <= dl ->
  let '(r, n, out, _) := buffToBuffDecompress junk (enc_stream e0 payload) dl small in
  (r, n, out) = (BZ_OK, Z.of_nat (length payload), payload).
Proof.
  intros small junk e0 payload dl [-> | ->]; [exact (rt_core false junk e0 payload dl)| exact (rt_core true junk e0 payload dl)].
Qed.

(* [comment removed for export] *)
Theorem enc_stream_bytes : forall e0 payload,
  E0OK' e0 -> SI (e_fin e0 (Z.of_nat (length payload))) -> bytes payload -> bytes_ok (enc_stream e0 payload).
Proof.
  intros e0 payload OK' HSI HB. cps_pose OK' as (OK & BN1 & NZ0 & CC0 & CH0).
  pose proof (START_fin e0 payload OK) as ST0.
  assert (RCH : CHAIN EB 1 (e_bw (e_fin e0 (Z.of_nat (length payload)))) (enc_blocks e0 payload)).
  { unfold enc_blocks. apply (run_chain EB SI SI_rl SI_entry); try assumption; lia. }
  cps_destruct (chain_bits EB body_ws BODY_ok ORIG_ok _ 1 _ RCH ltac:(lia) ltac:(intros; lia)) as (pad & _ & _ & BOK).
  exact BOK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem b2b_round_trip : forall a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM junk payload destLen dl small,
  zbok a1 -> zbok a2 -> bh_w32 ft -> bytes payload -> 0 < destLen -> Z.of_nat (length payload) <= dl -> small = 0 \/ small = 1 ->
  let e0 := est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM in
  let str := enc_stream e0 payload in
  (let '(ret, e', z') := bzCompress znew e0 (z_b2b payload destLen) BZ_FINISH in
   (Z.of_nat (length str) <= destLen ->
      ret = BzCDriver.BZ_STREAM_END /\ z_outr z' = rev str /\ z_avail_out z' = destLen - Z.of_nat (length str) /\ z_in z' = [] /\ z_avail_in z' = 0) /\
   (destLen < Z.of_nat (length str) ->
      ret = BZ_FINISH_OK /\ z_outr z' = rev (firstn (Z.to_nat destLen) str) /\ z_avail_out z' = 0)) /\
  (let '(r, n, out, _) := buffToBuffDecompress junk str dl small in (r, n, out) = (BZ_OK, Z.of_nat (length payload), payload)).
Proof.
  intros a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM junk payload destLen dl small Z1 Z2 FT BY DL LE SM.
  destruct (init_ok a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM Z1 Z2 FT) as [OK' SIn].
  cbv zeta. split.
  - apply b2b_bzCompress; [exact (proj1 OK')| exact DL| apply (run_numZ0 EB body_ws BODY_ok ORIG_ok SI SI_rl SI_entry); [exact OK'| apply SIn| exact BY]|].
    unfold enc_blocks. apply (run_fuel EB SI SI_rl SI_entry); [apply SIn| apply START_fin; exact (proj1 OK')| exact BY].
  - apply rt_small; [exact SM| exact OK'| apply SIn| exact BY| exact LE].
Qed.

(* [comment removed for export] *)
Corollary b2b_round_trip0 : forall sm payload destLen dl,
  bytes payload -> 0 < destLen -> Z.of_nat (length payload) <= dl ->
  let str := enc_stream est0 payload in
  (let '(ret, e', z') := bzCompress znew est0 (z_b2b payload destLen) BZ_FINISH in
   (Z.of_nat (length str) <= destLen ->
      ret = BzCDriver.BZ_STREAM_END /\ z_outr z' = rev str /\ z_avail_out z' = destLen - Z.of_nat (length str) /\ z_in z' = [] /\ z_avail_in z' = 0) /\
   (destLen < Z.of_nat (length str) ->
      ret = BZ_FINISH_OK /\ z_outr z' = rev (firstn (Z.to_nat destLen) str) /\ z_avail_out z' = 0)) /\
  decompress_b2b sm str dl = (BZ_OK, Z.of_nat (length payload), payload).
Proof.
  intros sm payload destLen dl BY DL LE. unfold est0, decompress_b2b.
  destruct (b2b_round_trip znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0 dst_zero payload destLen dl (if sm then 1 else 0)
              zbok_znew' zbok_znew' bh_w32_znew BY DL LE ltac:(destruct sm; [right| left]; reflexivity)) as [A B].
  cbv zeta in A, B. split; [exact A|].
  destruct (buffToBuffDecompress dst_zero _ dl _) as [[[r n] out] dd]. exact B.
Qed.
End BZPS.
