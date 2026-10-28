(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzLemmasT BzLemmasMtf.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5a.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR3aFs BzR1a BzR1e.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRT1.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ws_bhdr_e (crc op : Z) : list (Z * Z) :=
  [(8, 49); (8, 65); (8, 89); (8, 38); (8, 83); (8, 89)] ++ ws_u32 crc ++ [(1, 0); (24, op)].

Lemma cb_bhdr_wapp : forall b e1, cb_bhdr b e1 = wapp b (ws_bhdr_e (e_blockCRC e1) (e_origPtr e1)).
Proof. intros. reflexivity. Qed.
Lemma cb_hdr_eq : forall e1, cb_hdr e1 =
  (if e_blockNo e1 =? 1 then wapp (BW 0 0 (bw_numZ (e_bw e1)) (bw_zb (e_bw e1))) (ws_stream_hdr BLOCKSIZE100K) else e_bw e1).
Proof. intros. unfold cb_hdr, ws_stream_hdr, BZ_HDR_0. reflexivity. Qed.   (* [comment removed for export] *)
Lemma cb_trailer_eq : forall il b cc, cb_trailer il b cc = (if il then bs_finish BS_FUEL (wapp b (ws_eos cc)) else b).
Proof. intros. reflexivity. Qed.
End ACeilS1.

Ltac wleg1 := apply wlegal_cons; split; [split; [lia| try change (2 ^ 8) with 256; try change (2 ^ 1) with 2; lia]|].
Section ACeilS2. Context {BZP : BzParams}.

Lemma ws_bhdr_e_bits : forall crc op, 0 <= op < 2 ^ 24 -> wbits (ws_bhdr_e crc op) = wbits (ws_blk_hdr crc op).
Proof.
  intros crc op Hop. unfold ws_bhdr_e, ws_blk_hdr.
  set (L1 := [(8, 49); (8, 65); (8, 89); (8, 38); (8, 83); (8, 89)] ++ ws_u32 crc ++ [(1, 0)]).
  change ([(8, 49); (8, 65); (8, 89); (8, 38); (8, 83); (8, 89)] ++ ws_u32 crc ++ [(1, 0); (24, op)]) with (L1 ++ [(24, op)]).
  change ([(8, 49); (8, 65); (8, 89); (8, 38); (8, 83); (8, 89)] ++ ws_u32 crc ++ [(1, 0); (8, op / 65536); (8, (op / 256) mod 256); (8, op mod 256)])
    with (L1 ++ [(8, op / 65536); (8, (op / 256) mod 256); (8, op mod 256)]).
  assert (WL : wlegal L1).
  { subst L1. apply wlegal_app. split; [repeat wleg1; apply wlegal_nil|].
    apply wlegal_app. split; [apply ws_u32_legal|]. wleg1. apply wlegal_nil. }
  assert (W24 : wlegal [(24, op)]) by (apply wlegal_cons; split; [split; [lia| exact Hop]| apply wlegal_nil]).
  assert (W3 : wlegal [(8, op / 65536); (8, (op / 256) mod 256); (8, op mod 256)]).
  { pose proof (Z.mod_pos_bound op 256 ltac:(lia)). pose proof (Z.mod_pos_bound (op / 256) 256 ltac:(lia)).
    assert (0 <= op / 65536 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]; change (2 ^ 24) with 16777216 in Hop; lia]).
    change (2 ^ 8) with 256. repeat (apply wlegal_cons; split; [cbn -[Z.div Z.modulo]; change (2 ^ 8) with 256; lia|]). apply wlegal_nil. }
  rewrite (wbits_app L1 [(24, op)] WL W24), (wbits_app L1 _ WL W3). rewrite wbits_24_bytes by exact Hop. reflexivity.
Qed.

(* [comment removed for export] *)
Definition carry (b : bw) : bits := Bits (bw_live b) (bw_buff b / 2 ^ (32 - bw_live b)).
Lemma bw_abs_split : forall b, 0 <= bw_numZ b -> bw_abs b = bapp (bytes_bits (bw_bytes b)) (carry b).
Proof.
  intros b Hn. unfold bw_abs, bapp, bytes_bits, carry. cbn [b_len b_val]. rewrite bw_bytes_length, Z2Nat.id by lia. reflexivity.
Qed.
Lemma carry_reset : forall b, carry (BW (bw_buff b) (bw_live b) 0 znew) = carry b.
Proof. reflexivity. Qed.
Lemma bw_abs_reset : forall b, bw_abs (BW (bw_buff b) (bw_live b) 0 znew) = carry b.
Proof. intros b. rewrite bw_abs_split by (cbn; lia). unfold bw_bytes. cbn [bw_zb bw_numZ Z.to_nat zarr_to_list]. rewrite carry_reset. apply bapp_bnil_l. Qed.
Lemma bw_clean_reset : forall b, bw_clean b -> bw_clean (BW (bw_buff b) (bw_live b) 0 znew).
Proof. (intros b; cps_intros (A & B & C & D & E)). unfold bw_clean. cbn [bw_live bw_buff bw_numZ bw_bytes bw_zb Z.to_nat zarr_to_list]. repeat split; try lia. constructor. Qed.
(* [comment removed for export] *)
Lemma bytes_bits_app : forall l1 l2, bytes_bits (l1 ++ l2) = bapp (bytes_bits l1) (bytes_bits l2).
Proof. intros. unfold bytes_bits, bapp. cbn [b_len b_val]. rewrite length_app, bytes_val_app. f_equal. lia. Qed.
Lemma bytes_ok_app : forall l1 l2, bytes_ok l1 -> bytes_ok l2 -> bytes_ok (l1 ++ l2).
Proof. intros. unfold bytes_ok. apply Forall_app. split; assumption. Qed.

Section Blocks.
  (* [comment removed for export] *)
  Variable EB : est -> Prop.                      (* [comment removed for export] *)
  Variable body_ws : est -> list (Z * Z).        (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis BODY : forall e, EB e -> 0 < e_nblock e ->
    let e1 := cb_sorted e in
    let eg := fst (generateMTFValues (est_set_bw e1 (cb_bhdr (cb_hdr e1) e1)) znew) in
    e_bw (fst (sendMTFValues eg znew znew znew znew znew znew znew)) = wapp (cb_bhdr (cb_hdr e1) e1) (body_ws e) /\ wlegal (body_ws e).
  (* [comment removed for export] *)
  Hypothesis ORIG : forall e, EB e -> 0 < e_nblock e -> 0 <= e_origPtr (cb_sorted e) < 2 ^ 24.

  (* [comment removed for export] *)
  Definition blk_ws (e : est) : list (Z * Z) :=
    (if e_blockNo e =? 1 then ws_stream_hdr BLOCKSIZE100K else []) ++
    (if 0 <? e_nblock e then ws_bhdr_e (crc_final (e_blockCRC e)) (e_origPtr (cb_sorted e)) ++ body_ws e else []).
  (* [comment removed for export] *)
  Definition cc_after (e : est) : Z := if 0 <? e_nblock e then cc_next (e_combinedCRC e) (crc_final (e_blockCRC e)) else e_combinedCRC e.

  Lemma cb_sorted_more : forall e, e_blockCRC (cb_sorted e) = crc_final (e_blockCRC e) /\ e_combinedCRC (cb_sorted e) = cc_next (e_combinedCRC e) (crc_final (e_blockCRC e)).
  Proof.
    intros e. unfold cb_sorted. cps_destruct (blockSort_shape (cb_e0 e) znew) as (a1 & a2 & ft & op & E). rewrite E. cbn. split; reflexivity.
  Qed.
  Lemma sm_gm_cc : forall e c0 f0 p0 i0 h0 w0 q0 yy, e_combinedCRC (fst (sendMTFValues (fst (generateMTFValues e yy)) c0 f0 p0 i0 h0 w0 q0)) = e_combinedCRC e.
  Proof.
    intros. cps_destruct (gm_shape e yy) as (a & b & c & d & f & E). rewrite E.
    match goal with |- context [sendMTFValues ?ee] => cps_destruct (sm_shape ee c0 f0 p0 i0 h0 w0 q0) as (b1 & n1 & s1 & s2 & l1 & cd & rf & lp & E2); rewrite E2 end.
    reflexivity.
  Qed.
  Lemma BS_range : 1 <= BLOCKSIZE100K <= 9.
  Proof. bz_params. lia. Qed.
  Lemma ws_stream_hdr_legal : forall bs, 1 <= bs <= 9 -> wlegal (ws_stream_hdr bs).
  Proof. intros bs H. unfold ws_stream_hdr. repeat wleg1. apply wlegal_nil. Qed.
  Lemma ws_eos_legal : forall cc, wlegal (ws_eos cc).
  Proof. intros cc. unfold ws_eos. apply wlegal_app. split; [| apply ws_u32_legal]. repeat wleg1. apply wlegal_nil. Qed.
  Lemma ws_bhdr_e_legal : forall crc op, 0 <= op < 2 ^ 24 -> wlegal (ws_bhdr_e crc op).
  Proof.
    intros crc op Hop. unfold ws_bhdr_e. apply wlegal_app. split; [repeat wleg1; apply wlegal_nil|].
    apply wlegal_app. split; [apply ws_u32_legal|]. wleg1. apply wlegal_cons. split; [split; [lia| exact Hop]| apply wlegal_nil].
  Qed.
  Lemma blk_ws_legal : forall e, (0 < e_nblock e -> EB e) -> wlegal (blk_ws e).
  Proof.
    intros e HE. unfold blk_ws. apply wlegal_app. split.
    - destruct (e_blockNo e =? 1); [apply ws_stream_hdr_legal; apply BS_range| apply wlegal_nil].
    - destruct (Z.ltb_spec 0 (e_nblock e)) as [P|]; [| apply wlegal_nil]. specialize (HE P).
      apply wlegal_app. split; [apply ws_bhdr_e_legal; apply ORIG; assumption| exact (proj2 (BODY e HE P))].
  Qed.

  (* [comment removed for export] *)
  Theorem compressBlock_wapp : forall e is_last, (0 < e_nblock e -> EB e) -> bw_numZ (e_bw e) = 0 ->
    let b0 := if e_blockNo e =? 1 then BW 0 0 0 znew else BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew in
    let b1 := wapp b0 (blk_ws e) in
    blk_bw (e, is_last) = (if is_last then bs_finish BS_FUEL (wapp b1 (ws_eos (cc_after e))) else b1).
  Proof.
    intros e is_last HE NZ0. cbv zeta. unfold blk_bw. cbn [fst snd]. rewrite compressBlock_bw. unfold blk_ws, cc_after.
    cps_destruct (cb_sorted_fields e) as (F1 & F2 & F3 & F4). destruct (cb_sorted_more e) as [F5 F6].
    destruct (Z.ltb_spec 0 (e_nblock e)) as [P|Z0].
    - specialize (HE P). cbv zeta. destruct (BODY e HE P) as [BE BL]. rewrite BE, sm_gm_cc. cbn [e_combinedCRC est_set_bw]. rewrite F6.
      rewrite cb_trailer_eq, cb_bhdr_wapp, cb_hdr_eq, F2, F4, F5. cbn [bw_numZ bw_zb bw_buff bw_live].
      destruct (e_blockNo e =? 1), is_last; rewrite <- ?wapp_app, <- ?app_assoc; cbn [app]; reflexivity.
    - rewrite cb_trailer_eq, cb_hdr_eq. cbn [e_blockNo e_bw est_set_bw bw_numZ bw_zb bw_buff bw_live e_combinedCRC]. rewrite NZ0, !app_nil_r.
      destruct (e_blockNo e =? 1); [reflexivity|]. cbn [wapp]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Fixpoint CHAIN (k : Z) (bp : bw) (l : list (est * bool)) : Prop :=
    match l with
    | [] => False
    | (e, last) :: l' =>
        e_blockNo e = k /\ (0 < e_nblock e -> EB e) /\ bw_numZ (e_bw e) = 0 /\
        (1 < k -> bw_buff (e_bw e) = bw_buff bp /\ bw_live (e_bw e) = bw_live bp) /\
        match last with true => l' = [] | false => CHAIN (k + 1) (blk_bw (e, false)) l' end
    end.
  Fixpoint ws_all (l : list (est * bool)) : list (Z * Z) :=
    match l with [] => [] | (e, _) :: l' => blk_ws e ++ ws_all l' end.
  (* [comment removed for export] *)

  Lemma ws_all_legal : forall k bp l, CHAIN k bp l -> wlegal (ws_all l).
  Proof.
    intros k bp l. revert k bp. induction l as [|[e last] l IH]; intros k bp C; [apply wlegal_nil|].
    cbn [ws_all]. cps_destruct C as (K & HE & NZ & CB & NX). apply wlegal_app. split; [apply blk_ws_legal; exact HE|].
    destruct last; [subst l; apply wlegal_nil| eapply IH; exact NX].
  Qed.

  Fixpoint lastcc (d : Z) (l : list (est * bool)) : Z :=
    match l with [] => d | (e, _) :: l' => lastcc (cc_after e) l' end.
  Lemma lastcc_any : forall l d d', l <> [] -> lastcc d l = lastcc d' l.
  Proof. intros [|[e b] l] d d' H; [congruence| reflexivity]. Qed.

  Lemma bw_abs_zero : bw_abs (BW 0 0 0 znew) = bnil.
  Proof. reflexivity. Qed.
  Lemma bw_clean_zero : bw_clean (BW 0 0 0 znew).
  Proof. apply bw_clean_init; [lia| constructor]. Qed.

  Theorem chain_bits : forall l k bp, CHAIN k bp l -> 1 <= k -> (1 < k -> bw_clean bp) ->
    let c0 := if k =? 1 then bnil else carry bp in
    exists pad, 0 <= pad < 8 /\
      bytes_bits (enc_bytes l) = bapp (bapp c0 (wbits (ws_all l ++ ws_eos (lastcc 0 l)))) (Bits pad 0) /\
      bytes_ok (enc_bytes l).
  Proof.
    induction l as [|[e last] l IH]; intros k bp C Hk CL; [destruct C|].
    cbv zeta. cps_destruct C as (K & HE & NZ0 & CB & NX).
    pose proof (compressBlock_wapp e last HE NZ0) as CW. cbv zeta in CW.
    set (b0 := if e_blockNo e =? 1 then BW 0 0 0 znew else BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) in *.
    assert (B0 : bw_clean b0 /\ bw_abs b0 = (if k =? 1 then bnil else carry bp)).
    { subst b0. rewrite K. destruct (Z.eqb_spec k 1) as [E1|N1].
      - split; [apply bw_clean_zero| apply bw_abs_zero].
      - destruct (CB ltac:(lia)) as [E2 E3]. rewrite E2, E3. split; [apply bw_clean_reset; apply CL; lia| apply bw_abs_reset]. }
    destruct B0 as [C0 A0].
    pose proof (blk_ws_legal e HE) as WL.
    destruct (wapp_abs (blk_ws e) b0 WL C0) as [A1 C1]. rewrite A0 in A1.
    set (b1 := wapp b0 (blk_ws e)) in *.
    cbn [ws_all lastcc]. rewrite enc_bytes_cons.
    destruct last.
    - (* [comment removed for export] *)
      subst l. cbn [enc_bytes map concat ws_all lastcc]. rewrite !app_nil_r.
      pose proof (ws_eos_legal (cc_after e)) as WE.
      destruct (wapp_abs (ws_eos (cc_after e)) b1 WE C1) as [A2 C2]. rewrite A1 in A2.
      cps_destruct (bs_finish_abs (wapp b1 (ws_eos (cc_after e))) C2) as (pad & P1 & P2 & P3 & P4).
      exists pad. split; [exact P1|]. unfold blk_bytes. rewrite CW. split; [| exact P3].
      rewrite P2, A2. rewrite wbits_app by assumption. rewrite (bapp_assoc _ (wbits (blk_ws e))) by (apply wbits_len; assumption). reflexivity.
    - (* [comment removed for export] *)
      assert (CWF : blk_bw (e, false) = b1) by exact CW.
      rewrite CWF in NX.
      cps_destruct (IH (k + 1) b1 NX ltac:(lia) ltac:(intros; exact C1)) as (pad & P1 & P2 & P3).
      replace (k + 1 =? 1) with false in P2 by (symmetry; apply Z.eqb_neq; lia).
      exists pad. split; [exact P1|].
      assert (NE : l <> []) by (destruct l; [destruct NX| discriminate]).
      rewrite (lastcc_any l (cc_after e) 0 NE). unfold blk_bytes at 1 2. rewrite CWF.
      split.
      + rewrite bytes_bits_app, P2.
        pose proof (wbits_len (blk_ws e) WL) as L1.
        pose proof (wbits_len _ (proj2 (wlegal_app _ _) (conj (ws_all_legal _ _ _ NX) (ws_eos_legal (lastcc 0 l))))) as L2.
        cps_destruct C1 as (C1a & C1b & C1c & C1d & C1e).
        rewrite <- (bapp_assoc (bytes_bits (bw_bytes b1))); [| unfold bapp, carry; cbn [b_len]; lia| cbn [b_len]; lia].
        rewrite <- (bapp_assoc (bytes_bits (bw_bytes b1)) (carry b1)); [| unfold carry; cbn [b_len]; lia| exact L2].
        rewrite <- bw_abs_split by lia. rewrite A1.
        rewrite (bapp_assoc _ (wbits (blk_ws e))) by lia.
        rewrite <- app_assoc, (wbits_app (blk_ws e)) ; [reflexivity| exact WL|].
        apply wlegal_app. split; [eapply ws_all_legal; exact NX| apply ws_eos_legal].
      + apply bytes_ok_app; [| exact P3]. cps_destruct C1 as (C1a & C1b & C1c & C1d & C1e). exact C1e.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition bytes (l : list Z) : Prop := Forall (fun c => 0 <= c < 256) l.
  Lemma R1 : forall r c, RLI r -> 0 <= c < 256 -> (rl_ch r = 256 -> rl_nblock r = 0) ->
    RLI (add_char_to_block r c) /\ rl_data (add_char_to_block r c) ++ rl_pend (add_char_to_block r c) = rl_data r ++ rl_pend r ++ [c] /\
    rl_ch (add_char_to_block r c) = c.
  Proof. intros r c H Hc E. pose proof (add_char_RLI r c H Hc E) as X. cbv zeta in X. cps_destruct X as (A & B & _ & D & _). split; [exact A|]. split; [exact B| exact D]. Qed.
  Lemma R2 : forall r, RLI r -> RLI (flush_RL r) /\ rl_data (flush_RL r) = rl_data r ++ rl_pend r /\ rl_pend (flush_RL r) = [].
  Proof. intros r H. cps_pose (flush_RL_RLI r H) as (A & B & C & _). split; [exact A|]. split; [exact B| exact C]. Qed.
  Lemma R_empty : forall r, RLI r -> rl_nblock r = 0 -> rl_data r = [].
  Proof. intros r H N. unfold rl_data, rl_bytes. rewrite N. reflexivity. Qed.
  Lemma R_nneg : forall r, RLI r -> 0 <= rl_nblock r.
  Proof. intros r H. cps_pose (RLI_facts r H) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
  Lemma RLI_inv : forall r, RLI r -> rl_inv r.
  Proof. intros r H. cps_pose (RLI_facts r H) as (_ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.

  (* [comment removed for export] *)
  Variable SI : est -> Prop.
  (* [comment removed for export] *)
  Hypothesis SI_rl : forall s, SI s -> RLI (est_rl s).
  Hypothesis SI_entry : forall s inp, SI s -> START s inp -> bytes inp ->
    let '(e1, inp', last) := enc_entry s inp in (0 < e_nblock e1 -> EB e1) /\ (last = false -> SI (enc_next (enc_exit e1 false))).

  (* [comment removed for export] *)
  Variable READY : est -> dst -> Prop.
  Variable sm : bool.
  Definition DINV (d : dst) : Prop := d_bs100k d = BLOCKSIZE100K /\ smallb d = sm.
  (* [comment removed for export] *)
  Hypothesis BLK_DEC : forall e L d s rest,
    EB e -> 0 < e_nblock e -> DINV d -> rd_ok d s -> bits_ok rest ->
    rd_abs d s = bapp (wbits (ws_bhdr_e (crc_final (e_blockCRC e)) (e_origPtr (cb_sorted e)) ++ body_ws e)) rest ->
    exists k L' d' s1 kb, let dfin := d_set_sv d' L' in
      (forall f, drun (k + f) 14 L d s = dgo f (DRet BZ_OK L' d' s1)) /\ Z.of_nat k <= dcost d s d' s1 /\ consumed_from kb s s1 /\
      rd_abs d' s1 = rest /\ rd_ok d' s1 /\
      d_state dfin = BZ_X_OUTPUT /\ sv_nblock L' = e_nblock e /\ DINV dfin /\
      d_sbcrc dfin = crc_final (e_blockCRC e) /\ d_cccrc dfin = d_cccrc d /\
      READY e dfin.
  (* [comment removed for export] *)
  Hypothesis BLK_UNRLE : forall e dfin s,
    EB e -> 0 < e_nblock e -> READY e dfin -> Z.of_nat (length (rl_data (est_rl e))) <= s_avail_out s ->
    let seg := rl_data (est_rl e) in let len := Z.of_nat (length seg) in
    exists d'', unRLE dfin s = (0, d'', DSTRM (s_in s) (rev seg ++ s_out s) (s_avail_out s - len) (s_tin s) (s_tout s + len)) /\
      d_nused d'' = sv_nblock (d_sv dfin) + 1 /\ d_out_len d'' = 0 /\ d_cbcrc d'' = e_blockCRC e /\
      d_sv d'' = d_sv dfin /\ d_state d'' = d_state dfin /\ d_sbcrc d'' = d_sbcrc dfin /\ d_cccrc d'' = d_cccrc dfin /\
      d_bsBuff d'' = d_bsBuff dfin /\ d_bsLive d'' = d_bsLive dfin /\ d_bs100k d'' = d_bs100k dfin /\ d_small d'' = d_small dfin.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rle_fill_data : forall fuel r inp, RLI r -> bytes inp -> (rl_ch r = 256 -> rl_nblock r = 0) ->
    let '(r', inp') := rle_fill fuel r inp in
    RLI r' /\ rl_data r' ++ rl_pend r' = rl_data r ++ rl_pend r ++ firstn (length inp - length inp') inp /\
    (rl_ch r' = 256 -> rl_nblock r' = 0).
  Proof.
    induction fuel as [|f IH]; intros r inp HR HB HE; cbn [rle_fill].
    - rewrite Nat.sub_diag. cbn. rewrite app_nil_r. split; [exact HR|]. split; [reflexivity| exact HE].
    - destruct (NBLOCKMAX <=? rl_nblock r). { rewrite Nat.sub_diag. cbn. rewrite app_nil_r. split; [exact HR|]. split; [reflexivity| exact HE]. }
      destruct inp as [|c rest]. { cbn. rewrite app_nil_r. split; [exact HR|]. split; [reflexivity| exact HE]. }
      apply Forall_cons_iff in HB as [Hc HB]. cps_destruct (R1 r c HR Hc HE) as (HR' & E1 & CH).
      specialize (IH (add_char_to_block r c) rest HR' HB ltac:(intros X; rewrite CH in X; lia)).
      cps_pose (rle_fill_suffix f (add_char_to_block r c) rest) as (k & SK & LK).
      destruct (rle_fill f (add_char_to_block r c) rest) as [r' inp']. cbn [snd] in SK. cps_destruct IH as (I1 & I2 & I3).
      split; [exact I1|]. split; [| exact I3].
      rewrite I2, app_assoc, E1. assert (LI : (length inp' <= length rest)%nat) by (rewrite SK, length_skipn; lia).
      cbn [length]. replace (S (length rest) - length inp')%nat with (S (length rest - length inp')) by lia. cbn [firstn].
      rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma enc_entry_data : forall s inp, SI s -> START s inp -> bytes inp ->
    let '(e1, inp', last) := enc_entry s inp in
    rl_data (est_rl e1) ++ rl_pend (est_rl e1) = rl_pend (est_rl s) ++ firstn (length inp - length inp') inp /\
    (last = true -> rl_pend (est_rl e1) = []) /\ RLI (est_rl e1) /\
    (exists k, inp' = skipn k inp /\ (length inp' = length inp - k)%nat).
  Proof.
    intros s inp HS ST HB. cps_pose ST as (M & S & X & NB & OP). unfold enc_entry.
    pose proof (rle_fill_data (Datatypes.S (length inp)) (est_rl s) inp (SI_rl s HS) HB ltac:(intros _; rewrite rl_nblock_est_rl; exact NB)) as F.
    cps_pose (rle_fill_suffix (Datatypes.S (length inp)) (est_rl s) inp) as (k & SK & LK).
    destruct (rle_fill _ (est_rl s) inp) as [r' inp']. cbn [snd] in SK. cps_destruct F as (F1 & F2 & _).
    rewrite (R_empty (est_rl s) (SI_rl s HS)) in F2 by (rewrite rl_nblock_est_rl; exact NB). cbn [app] in F2.
    assert (LI : (length inp' = length inp - k)%nat) by (rewrite SK, length_skipn; lia).
    destruct inp' as [|c rest].
    - rewrite !est_rl_set_rl. cps_destruct (R2 r' F1) as (G1 & G2 & G3). rewrite G2, G3, app_nil_r, F2.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact G1|]. exists k. split; [exact SK| exact LI].
    - rewrite est_rl_set_rl, F2. split; [reflexivity|]. split; [intros; discriminate|]. split; [exact F1|].
      exists k. split; [exact SK| exact LI].
  Qed.

  Lemma rl_pend_next : forall e1 last, rl_pend (est_rl (enc_next (enc_exit e1 last))) = rl_pend (est_rl e1).
  Proof.
    intros e1 last. pose proof (enc_next_fields (enc_exit e1 last)) as F. cbv zeta in F.
    cps_destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fch & Flen & _).
    pose proof (cb_keep e1 last) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & _ & Kch & Klen & _).
    unfold rl_pend. cbn [rl_ch rl_len est_rl]. rewrite Fch, Flen. unfold enc_exit. cbn [e_state_in_ch e_state_in_len est_set_modes]. rewrite Kch, Klen. reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition blk_ws' (e : est) : list (Z * Z) :=
    if 0 <? e_nblock e then ws_bhdr_e (crc_final (e_blockCRC e)) (e_origPtr (cb_sorted e)) ++ body_ws e else [].
  Fixpoint ws_all' (l : list (est * bool)) : list (Z * Z) :=
    match l with [] => [] | (e, _) :: l' => blk_ws' e ++ ws_all' l' end.
  Lemma blk_ws_split : forall e, blk_ws e = (if e_blockNo e =? 1 then ws_stream_hdr BLOCKSIZE100K else []) ++ blk_ws' e.
  Proof. reflexivity. Qed.
  Lemma ws_all_tail : forall l k bp, CHAIN k bp l -> 2 <= k -> ws_all l = ws_all' l.
  Proof.
    induction l as [|[e last] l IH]; intros k bp C Hk; [reflexivity|].
    cps_destruct C as (K & _ & _ & _ & NX). cbn [ws_all ws_all']. rewrite blk_ws_split, K.
    replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app]. f_equal.
    destruct last; [subst l; reflexivity| eapply IH; [exact NX| lia]].
  Qed.
  Lemma ws_all_head : forall e last l bp, CHAIN 1 bp ((e, last) :: l) -> ws_all ((e, last) :: l) = ws_stream_hdr BLOCKSIZE100K ++ ws_all' ((e, last) :: l).
  Proof.
    intros e last l bp C. cps_destruct C as (K & _ & _ & _ & NX). cbn [ws_all ws_all']. rewrite blk_ws_split, K, Z.eqb_refl, <- app_assoc. f_equal. f_equal.
    destruct last; [subst l; reflexivity| eapply ws_all_tail; [exact NX| lia]].
  Qed.
  Lemma blk_ws'_legal : forall e, (0 < e_nblock e -> EB e) -> wlegal (blk_ws' e).
  Proof.
    intros e HE. unfold blk_ws'. destruct (Z.ltb_spec 0 (e_nblock e)) as [P|]; [| apply wlegal_nil]. specialize (HE P).
    apply wlegal_app. split; [apply ws_bhdr_e_legal; apply ORIG; assumption| exact (proj2 (BODY e HE P))].
  Qed.

  Definition dwrap (r : dres) : Z * dst * dstrm :=
    match r with
    | DGo _ L' d' s' => (BZ_OK, d_set_sv d' L', s')
    | DRet rv L' d' s' => (rv, d_set_sv d' L', s')
    | DRetNoSave rv _ d' s' => (rv, d', s')
    end.
  Definition bzd_cont (f : nat) (x : Z * dst * dstrm) : Z * dst * dstrm :=
    let '(r, d2, s2) := x in
    if r =? BZ_STREAM_END then (if d_cccrc d2 =? d_sccrc d2 then (r, d2, s2) else (BZ_DATA_ERROR, d2, s2))
    else if negb (d_state d2 =? BZ_X_OUTPUT) then (r, d2, s2) else bzd_loop f d2 s2.

  Lemma d_sv_set_sv : forall d v, d_sv (d_set_sv d v) = v. Proof. intros; destruct d; reflexivity. Qed.
  Lemma d_state_set_sv : forall d v, d_state (d_set_sv d v) = d_state d. Proof. intros; destruct d; reflexivity. Qed.

  Lemma decompress_from : forall d s, d_state d <> BZ_X_MAGIC_1 ->
    decompress d s = dwrap (drun (9 * length (s_in s) + 64) (d_state d) (d_sv d) d s).
  Proof.
    intros d s H. unfold decompress. replace (d_state d =? BZ_X_MAGIC_1) with false by (symmetry; apply Z.eqb_neq; exact H).
    cbv zeta. unfold dwrap. destruct (drun _ _ _ d s); reflexivity.
  Qed.
  Lemma decompress_first : forall d s, d_state d = BZ_X_MAGIC_1 ->
    decompress d s = dwrap (drun (9 * length (s_in s) + 64) BZ_X_MAGIC_1 dsv_zero (d_set_sv d dsv_zero) s).
  Proof.
    intros d s H. unfold decompress. rewrite H, Z.eqb_refl. cbv zeta. rewrite d_sv_set_sv, d_state_set_sv, H.
    unfold dwrap. destruct (drun _ _ _ _ s); reflexivity.
  Qed.
  Lemma bzd_loop_first : forall f d s, d_state d = BZ_X_MAGIC_1 -> bzd_loop (S f) d s = bzd_cont f (decompress d s).
  Proof.
    intros f d s H. cbn [bzd_loop]. rewrite H. change (BZ_X_MAGIC_1 =? BZ_X_IDLE) with false. change (BZ_X_MAGIC_1 =? BZ_X_OUTPUT) with false.
    cbv iota beta. rewrite H. change (BZ_X_MAGIC_1 <=? BZ_X_MAGIC_1) with true. cbv iota. unfold bzd_cont. destruct (decompress d s) as [[r d2] s2]. reflexivity.
  Qed.
  Lemma bzd_loop_output : forall f d s, d_state d = BZ_X_OUTPUT ->
    bzd_loop (S f) d s =
      let '(corrupt, d', s') := unRLE d s in
      if corrupt =? 1 then (BZ_DATA_ERROR, d', s')
      else if (d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0) then
        let crc := crc_final (d_cbcrc d') in let d'' := d_set_cbcrc d' crc in
        if negb (crc =? d_sbcrc d'') then (BZ_DATA_ERROR, d'', s')
        else let cc := Z.lxor (Z.lor (Z.shiftl (d_cccrc d'') 1) (Z.shiftr (d_cccrc d'') 31) mod 4294967296) crc in
             bzd_cont f (decompress (d_set_state (d_set_cccrc d'' cc) BZ_X_BLKHDR_1) s')
      else (BZ_OK, d', s').
  Proof.
    intros f d s H. cbn [bzd_loop]. rewrite H. change (BZ_X_OUTPUT =? BZ_X_IDLE) with false. rewrite Z.eqb_refl. cbv iota beta.
    destruct (unRLE d s) as [[corrupt d'] s']. destruct (corrupt =? 1); [reflexivity|].
    destruct ((d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0))%bool; [| reflexivity]. cbv zeta.
    destruct (negb (crc_final (d_cbcrc d') =? d_sbcrc (d_set_cbcrc d' (crc_final (d_cbcrc d'))))); [reflexivity|].
    match goal with |- context [BZ_X_MAGIC_1 <=? d_state ?x] => replace (d_state x) with BZ_X_BLKHDR_1 by (destruct d'; reflexivity) end.
    change (BZ_X_MAGIC_1 <=? BZ_X_BLKHDR_1) with true. cbv iota. unfold bzd_cont.
    destruct (decompress _ s') as [[r d2] s2]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cc_forms : forall c x, 0 <= c < 4294967296 ->
    Z.lxor (Z.lor (Z.shiftl c 1) (Z.shiftr c 31) mod 4294967296) x = cc_next c x.
  Proof.
    intros c x Hc. unfold cc_next. f_equal.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 31) with 2147483648.
    assert (B : 0 <= c / 2147483648 < 2) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    rewrite (lor_disjoint (c * 2) (c / 2147483648) 1); try lia. 2:{ change (2 ^ 1) with 2. apply Z.mod_mul. lia. }
    rewrite (lor_disjoint ((c * 2) mod 4294967296) (c / 2147483648) 1); try lia.
    2:{ apply Z.mod_pos_bound. lia. }
    2:{ change (2 ^ 1) with 2. pose proof (Z.div_mod (c * 2) 4294967296 ltac:(lia)) as D. set (q := c * 2 / 4294967296) in D.
        replace ((c * 2) mod 4294967296) with ((c - 2147483648 * q) * 2) by lia. apply Z.mod_mul. lia. }
    change 4294967296 with (2 * 2147483648).
    pose proof (Z.div_mod c 2147483648 ltac:(lia)). pose proof (Z.mod_pos_bound c 2147483648 ltac:(lia)).
    destruct (Z.eq_dec (c / 2147483648) 0) as [E|E].
    - rewrite E in *. rewrite (Z.mod_small (c * 2)), (Z.mod_small (c * 2 + 0)) by lia. lia.
    - assert (E1 : c / 2147483648 = 1) by lia. rewrite E1 in *.
      replace (c * 2) with ((c mod 2147483648) * 2 + 1 * (2 * 2147483648)) by lia. rewrite Z_mod_plus_full.
      replace (c mod 2147483648 * 2 + 1 * (2 * 2147483648) + 1) with ((c mod 2147483648 * 2 + 1) + 1 * (2 * 2147483648)) by lia.
      rewrite Z_mod_plus_full. rewrite (Z.mod_small (_ * 2 + 1)), (Z.mod_small (_ * 2)) by lia. lia.
  Qed.

  Lemma rd_abs_ext : forall d1 d2 s1 s2, d_bsBuff d1 = d_bsBuff d2 -> d_bsLive d1 = d_bsLive d2 -> s_in s1 = s_in s2 -> rd_abs d1 s1 = rd_abs d2 s2.
  Proof. intros d1 d2 s1 s2 A B C. unfold rd_abs. rewrite A, B, C. reflexivity. Qed.
  Lemma rd_ok_ext : forall d1 d2 s1 s2, d_bsBuff d1 = d_bsBuff d2 -> d_bsLive d1 = d_bsLive d2 -> s_in s1 = s_in s2 -> rd_ok d1 s1 -> rd_ok d2 s2.
  Proof. intros d1 d2 s1 s2 A B C H. unfold rd_ok in *. rewrite <- A, <- B, <- C. exact H. Qed.
  Lemma pad_ok : forall pad, 0 <= pad < 8 -> bits_ok (Bits pad 0).
  Proof. intros pad H. unfold bits_ok. cbn. pose proof (pow2_pos pad ltac:(lia)). lia. Qed.
  Lemma drun_enough : forall k F lbl L d s r, (forall f, drun (k + f) lbl L d s = dgo f r) -> (k <= F)%nat ->
    match r with DGo _ _ _ _ => False | _ => True end -> drun F lbl L d s = r.
  Proof.
    intros k F lbl L d s r RUN LE NR. replace F with (k + (F - k))%nat by lia. rewrite RUN. destruct r; [destruct NR| reflexivity| reflexivity].
  Qed.
  Lemma dcost_bound : forall d s d1 s1, rd_ok d s -> 0 <= b_len (rd_abs d1 s1) -> (length (s_in s1) <= length (s_in s))%nat ->
    dcost d s d1 s1 <= d_bsLive d + 9 * Z.of_nat (length (s_in s)).
  Proof. intros d s d1 s1 (R1' & _) L LEN. unfold dcost. unfold rd_abs at 1. cbn [b_len]. lia. Qed.

  Lemma cc_next_range : forall c x, 0 <= c < 4294967296 -> 0 <= x < 4294967296 -> 0 <= cc_next c x < 4294967296.
  Proof.
    intros c x Hc Hx. unfold cc_next. change 4294967296 with (2 ^ 32). apply lxor_lt_pow2; [| change (2 ^ 32) with 4294967296; lia].
    apply lor_lt_pow2.
    - pose proof (Z.mod_pos_bound (Z.shiftl c 1) 4294967296 ltac:(lia)). change (2 ^ 32) with 4294967296. lia.
    - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 31 * 2 ^ 32) with (2 ^ 63). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dec_eos : forall cc L d s rest, 0 <= cc < 4294967296 -> rd_ok d s -> bits_ok rest -> rd_abs d s = bapp (wbits (ws_eos cc)) rest ->
    exists k d' s1 kb, (forall f, drun (k + f) 14 L d s = dgo f (DRet BZ_STREAM_END L d' s1)) /\ Z.of_nat k <= dcost d s d' s1 /\
      consumed_from kb s s1 /\ d_sccrc d' = cc /\ d_cccrc d' = d_cccrc d /\ rd_ok d' s1 /\ rd_abs d' s1 = rest.
  Proof.
    intros cc L d s rest Hcc RO BO AB.
    cps_destruct (drun_feed (ws_eos cc) 14 L d s rest _ (ws_eos_legal cc) RO BO AB (seg_eos cc L d s Hcc)) as (k & B & V & s1 & kb & RUN & REST & CF).
    exists k, (setLB (d_set_state (d_set_sccrc d cc) BZ_X_IDLE) B V), s1, kb.
    cps_destruct (REST d) as (R1' & R2' & R3').
    split; [intros f; rewrite RUN; reflexivity|]. split; [rewrite (dcost_LB d s _ d); exact R3'|]. split; [exact CF|].
    split; [rewrite lbg_sccrc; destruct d; reflexivity|]. split; [rewrite lbg_cccrc; destruct d; reflexivity|].
    split; [eapply rd_ok_LB; exact R2'| rewrite (rd_abs_LB _ d); exact R1'].
  Qed.

  (* [comment removed for export] *)
  Hypothesis EB_crc : forall e, EB e -> 0 <= e_blockCRC e < 4294967296.
  Hypothesis SI_cc : forall s, SI s -> 0 <= e_combinedCRC s < 4294967296.

  Lemma e_cc_next : forall e1 last, e_combinedCRC (enc_next (enc_exit e1 last)) = cc_after e1.
  Proof.
    intros e1 last. pose proof (enc_next_fields (enc_exit e1 last)) as F. cbv zeta in F. cps_destruct F as (_ & _ & _ & _ & _ & _ & Fcc & _).
    pose proof (cb_keep e1 last) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kcc).
    rewrite Fcc. unfold enc_exit. cbn [e_combinedCRC est_set_modes]. rewrite Kcc. reflexivity.
  Qed.
  Lemma enc_entry_keep : forall s inp, let '(e1, inp', last) := enc_entry s inp in
    e_combinedCRC e1 = e_combinedCRC s /\ e_bw e1 = e_bw s /\ e_blockNo e1 = e_blockNo s.
  Proof.
    intros s inp. unfold enc_entry. destruct (rle_fill _ _ inp) as [r' [|c rest]]; destruct s; cbn; repeat split; reflexivity.
  Qed.
  Lemma consumed_fields : forall kb s s1, consumed_from kb s s1 -> s_out s1 = s_out s /\ s_avail_out s1 = s_avail_out s /\ s_tout s1 = s_tout s /\ (length (s_in s1) <= length (s_in s))%nat.
  Proof. intros kb s s1 CF. unfold consumed_from in CF. rewrite CF. destruct s; cbn. rewrite length_skipn. repeat split; try reflexivity. lia. Qed.

  Lemma bytes_skipn : forall k l, bytes l -> bytes (skipn k l).
  Proof. induction k as [|k IH]; intros [|x l] H; [exact H| exact H| constructor|]. cbn [skipn]. apply IH. apply Forall_cons_iff in H. unfold bytes. tauto. Qed.

  (* [comment removed for export] *)
  Lemma run_step : forall s inp, SI s -> START s inp -> bytes inp ->
    let '(e1, inp', last) := enc_entry s inp in
    last = false -> SI (enc_next (enc_exit e1 false)) /\ START (enc_next (enc_exit e1 false)) inp' /\ bytes inp' /\ (length inp' < length inp)%nat.
  Proof.
    intros s inp HS ST HB. pose proof (SI_entry s inp HS ST HB) as SE. pose proof (EXIT_entry s inp ST) as EX. pose proof (enc_entry_data s inp HS ST HB) as ED.
    destruct (enc_entry s inp) as [[e1 inp'] last]. intros HL. destruct SE as [_ SEN]. destruct EX as [EX LT]. cps_destruct ED as (_ & _ & _ & k & SK & _).
    split; [exact (SEN HL)|]. split; [subst last; apply START_next; exact EX|]. split; [rewrite SK; apply bytes_skipn; exact HB| exact (LT HL)].
  Qed.
  Lemma run_legal : forall m s inp, SI s -> START s inp -> bytes inp -> wlegal (ws_all' (enc_run m s inp)).
  Proof.
    induction m as [|m IH]; intros s inp HS ST HB; [apply wlegal_nil|]. cbn [enc_run].
    pose proof (SI_entry s inp HS ST HB) as SE. pose proof (run_step s inp HS ST HB) as RS.
    destruct (enc_entry s inp) as [[e1 inp'] last]. destruct SE as [SEB _]. cbn [ws_all'].
    apply wlegal_app. split; [apply blk_ws'_legal; exact SEB|]. destruct last; [apply wlegal_nil|].
    cps_destruct (RS eq_refl) as (A & B & C & _). apply IH; assumption.
  Qed.


  Lemma firstn_sub_skipn : forall (k : nat) (l : list Z), firstn (length l - length (skipn k l)) l = firstn k l.
  Proof.
    intros k l. rewrite length_skipn. destruct (Nat.le_gt_cases k (length l)) as [H|H].
    - replace (length l - (length l - k))%nat with k by lia. reflexivity.
    - replace (length l - (length l - k))%nat with (length l) by lia. rewrite firstn_all, firstn_all2 by lia. reflexivity.
  Qed.
  Lemma d_sbcrc_set_cbcrc : forall d v, d_sbcrc (d_set_cbcrc d v) = d_sbcrc d. Proof. intros; destruct d; reflexivity. Qed.
  Lemma d_cccrc_set_cbcrc : forall d v, d_cccrc (d_set_cbcrc d v) = d_cccrc d. Proof. intros; destruct d; reflexivity. Qed.
  Lemma d_fields_14 : forall d crc cc, let d1 := d_set_state (d_set_cccrc (d_set_cbcrc d crc) cc) BZ_X_BLKHDR_1 in
    d_state d1 = BZ_X_BLKHDR_1 /\ d_cccrc d1 = cc /\ d_sv d1 = d_sv d /\ d_bsBuff d1 = d_bsBuff d /\ d_bsLive d1 = d_bsLive d /\
    d_bs100k d1 = d_bs100k d /\ d_small d1 = d_small d.
  Proof. intros; destruct d; repeat split; reflexivity. Qed.
  Lemma d_fields_sv : forall d v, d_bsBuff (d_set_sv d v) = d_bsBuff d /\ d_bsLive (d_set_sv d v) = d_bsLive d /\ d_cccrc (d_set_sv d v) = d_cccrc d /\
    d_sccrc (d_set_sv d v) = d_sccrc d /\ d_bs100k (d_set_sv d v) = d_bs100k d /\ d_small (d_set_sv d v) = d_small d.
  Proof. intros; destruct d; repeat split; reflexivity. Qed.
  Lemma DINV_ext : forall d1 d2, d_bs100k d1 = d_bs100k d2 -> d_small d1 = d_small d2 -> DINV d2 -> DINV d1.
  Proof. intros d1 d2 A B [C D]. unfold DINV, smallb in *. rewrite A, B. split; assumption. Qed.
  Lemma enc_run_ne : forall n s inp, (length inp < n)%nat -> enc_run n s inp <> [].
  Proof. intros [|n] s inp H; [lia|]. cbn [enc_run]. destruct (enc_entry s inp) as [[e1 i'] l']. discriminate. Qed.

  (* [comment removed for export] *)
  Lemma dec_core : forall n f s inp (F : nat) L d st out,
    SI s -> START s inp -> bytes inp -> (length inp < n)%nat ->
    let l := enc_run n s inp in
    (length l < f)%nat ->
    DINV d -> rd_ok d st ->
    (exists pad, 0 <= pad < 8 /\ rd_abs d st = bapp (wbits (ws_all' l ++ ws_eos (lastcc 0 l))) (Bits pad 0)) ->
    d_cccrc d = e_combinedCRC s ->
    d_bsLive d + 9 * Z.of_nat (length (s_in st)) <= Z.of_nat F ->
    s_out st = rev out ->
    Z.of_nat (length (rl_pend (est_rl s) ++ inp)) <= s_avail_out st ->
    exists d2 s2, bzd_cont f (dwrap (drun F 14 L d st)) = (BZ_STREAM_END, d2, s2) /\
      d_cccrc d2 = d_sccrc d2 /\
      s_out s2 = rev (out ++ rl_pend (est_rl s) ++ inp) /\
      s_avail_out s2 = s_avail_out st - Z.of_nat (length (rl_pend (est_rl s) ++ inp)).
  Proof.
    induction n as [|n IH]; intros f s inp F L d st out HS ST HB LN; [lia|]. cbv zeta. (intros LF DI RO; cps_intros (pad & PAD & AB); intros CC HF OUT AV).
    pose proof (SI_entry s inp HS ST HB) as SE. pose proof (enc_entry_data s inp HS ST HB) as ED. pose proof (EXIT_entry s inp ST) as EX.
    pose proof (enc_entry_facts s inp ST) as EF. pose proof (enc_entry_keep s inp) as EK. pose proof (run_step s inp HS ST HB) as RS0.
    cbn [enc_run] in LF, AB |- *.
    destruct (enc_entry s inp) as [[e1 inp'] last]. destruct SE as [SEB SEN]. cps_destruct ED as (D1 & D2 & D3 & kc & SK & LK). destruct EX as [EX LT'].
    cps_destruct EF as (_ & _ & _ & _ & _ & EFT & EFF). cps_destruct EK as (Kcc & Kbw & Kno).
    pose proof (SI_cc s HS) as CCR. pose proof (pad_ok pad PAD) as POK.
    rewrite length_app in AV.
    assert (LD : (length (rl_data (est_rl e1)) + length (rl_pend (est_rl e1)) = length (rl_pend (est_rl s)) + (length inp - length inp'))%nat).
    { pose proof (f_equal (@length Z) D1) as X. rewrite !length_app, length_firstn in X. lia. }
    assert (FI : firstn (length inp - length inp') inp ++ inp' = inp).
    { rewrite SK, firstn_sub_skipn. apply firstn_skipn. }
    cbn [ws_all' lastcc] in AB.
    destruct (Z.ltb_spec 0 (e_nblock e1)) as [NBP|NB0].
    - (* [comment removed for export] *)
      specialize (SEB NBP). pose proof (EB_crc e1 SEB) as BCR.
      unfold blk_ws' in AB at 1. replace (0 <? e_nblock e1) with true in AB by (symmetry; apply Z.ltb_lt; exact NBP).
      set (rest := if last then [] else enc_run n (enc_next (enc_exit e1 false)) inp') in *.
      rewrite <- (app_assoc (_ ++ body_ws e1) (ws_all' rest)) in AB.
      set (tailw := ws_all' rest ++ ws_eos (lastcc (cc_after e1) rest)) in AB.
      assert (WLh : wlegal (ws_bhdr_e (crc_final (e_blockCRC e1)) (e_origPtr (cb_sorted e1)) ++ body_ws e1)).
      { apply wlegal_app. split; [apply ws_bhdr_e_legal; apply ORIG; assumption| exact (proj2 (BODY e1 SEB NBP))]. }
      assert (WLt : wlegal tailw).
      { subst tailw. apply wlegal_app. split; [| apply ws_eos_legal]. subst rest. destruct last; [apply wlegal_nil|].
        cps_destruct (RS0 eq_refl) as (A & B & C & _). apply run_legal; assumption. }
      rewrite (wbits_app _ _ WLh WLt), bapp_assoc in AB by (try apply wbits_len; try exact WLt; cbn; lia).
      assert (BOK : bits_ok (bapp (wbits tailw) (Bits pad 0))) by (apply bapp_ok; [apply wbits_ok; exact WLt| exact POK]).
      cps_destruct (BLK_DEC e1 L d st _ SEB NBP DI RO BOK AB) as (k1 & L' & d' & s1 & kb & RUN & COST & CF & AB1 & RO1 & STo & NBo & DI1 & SB1 & CC1 & RDY).
      cps_pose (consumed_fields kb st s1 CF) as (CF1 & CF2 & CF3 & CF4).
      assert (K1 : (k1 <= F)%nat).
      { pose proof (dcost_bound d st d' s1 RO ltac:(rewrite AB1; exact (proj1 BOK)) CF4). lia. }
      rewrite (drun_enough k1 F 14 L d st _ RUN K1 I). cbn [dwrap]. unfold bzd_cont at 1.
      change (BZ_OK =? BZ_STREAM_END) with false. rewrite STo. change (negb (BZ_X_OUTPUT =? BZ_X_OUTPUT)) with false. cbv iota.
      destruct f as [|f']; [cbn [length] in LF; lia|]. rewrite bzd_loop_output by exact STo.
      cps_destruct (BLK_UNRLE e1 (d_set_sv d' L') s1 SEB NBP RDY ltac:(rewrite CF2; lia)) as (d'' & UN & NU & OL & CB & SV & STT & SB & CCC & BB & BL & BS & SM).
      rewrite UN. change (0 =? 1) with false. cbv iota. rewrite NU, SV, OL, !Z.eqb_refl. cbn [andb]. cbv iota zeta.
      rewrite CB, d_sbcrc_set_cbcrc, SB, SB1, Z.eqb_refl. cbn [negb]. cbv iota.
      rewrite d_cccrc_set_cbcrc, CCC, CC1, CC, <- Kcc, (cc_forms (e_combinedCRC e1) (crc_final (e_blockCRC e1)) ltac:(rewrite Kcc; exact CCR)).
      match goal with |- context [decompress ?dd ?ss] => set (d1 := dd); set (s1' := ss) end.
      pose proof (d_fields_14 d'' (crc_final (e_blockCRC e1)) (cc_next (e_combinedCRC e1) (crc_final (e_blockCRC e1)))) as DF. cbv zeta in DF. fold d1 in DF.
      cps_destruct DF as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
      cps_pose (d_fields_sv d' L') as (G1 & G2 & G3 & G4 & G5 & G6).
      assert (CA : cc_next (e_combinedCRC e1) (crc_final (e_blockCRC e1)) = cc_after e1) by (unfold cc_after; replace (0 <? e_nblock e1) with true by (symmetry; apply Z.ltb_lt; exact NBP); reflexivity).
      rewrite CA in F2.
      assert (RO2 : rd_ok d1 s1') by (eapply (rd_ok_ext d'); [rewrite F4, BB, G1| rewrite F5, BL, G2| subst s1'; cbn| exact RO1]; reflexivity).
      assert (AB2 : rd_abs d1 s1' = bapp (wbits tailw) (Bits pad 0)) by (rewrite <- AB1; apply rd_abs_ext; [rewrite F4, BB, G1| rewrite F5, BL, G2| subst s1'; cbn]; reflexivity).
      assert (DI2 : DINV d1) by (eapply DINV_ext; [rewrite F6, BS, G5| rewrite F7, SM, G6| exact DI1]; reflexivity).
      assert (CAR : 0 <= cc_after e1 < 4294967296) by (rewrite <- CA; apply cc_next_range; [rewrite Kcc; exact CCR| apply crc_final_range; exact BCR]).
      rewrite decompress_from by (rewrite F1; discriminate). rewrite F1, F3, SV, d_sv_set_sv. change BZ_X_BLKHDR_1 with 14.
      assert (BL2 : d_bsLive d1 <= 32) by (destruct RO2 as (X & _); lia).
      destruct last.
      + (* [comment removed for export] *)
        subst rest. cbn [ws_all' lastcc app] in tailw. subst tailw.
        cps_destruct (dec_eos (cc_after e1) L' d1 s1' (Bits pad 0) CAR RO2 POK AB2) as (k2 & d3 & s3 & kb2 & RUN2 & COST2 & CF5 & SCC & CCC2 & RO3 & AB3).
        cps_pose (consumed_fields kb2 s1' s3 CF5) as (CG1 & CG2 & CG3 & CG4).
        assert (K2 : (k2 <= 9 * length (s_in s1') + 64)%nat).
        { pose proof (dcost_bound d1 s1' d3 s3 RO2 ltac:(rewrite AB3; cbn; lia) CG4). lia. }
        rewrite (drun_enough k2 _ 14 L' d1 s1' _ RUN2 K2 I). cbn [dwrap]. unfold bzd_cont.
        rewrite Z.eqb_refl. cps_pose (d_fields_sv d3 L') as (_ & _ & J3 & J4 & _). rewrite J3, J4, CCC2, F2, SCC, Z.eqb_refl.
        exists (d_set_sv d3 L'), s3. split; [reflexivity|]. split; [rewrite J3, J4, CCC2, F2, SCC; reflexivity|].
        destruct (EFT eq_refl) as [-> _]. pose proof (D2 eq_refl) as P0.
        rewrite P0, app_nil_r in D1. rewrite P0 in LD. cbn [length] in LD, D1. rewrite Nat.sub_0_r, firstn_all in D1. rewrite Nat.sub_0_r in LD.
        rewrite CG1, CG2. subst s1'. cbn [s_out s_avail_out]. rewrite CF1, CF2, OUT, <- D1, rev_app_distr.
        split; reflexivity.
      + (* [comment removed for export] *)
        cps_destruct (RS0 eq_refl) as (HS' & ST' & HB' & LT'').
        assert (NE : rest <> []) by (subst rest; apply enc_run_ne; lia).
        specialize (IH f' (enc_next (enc_exit e1 false)) inp' (9 * length (s_in s1') + 64)%nat L' d1 s1' (out ++ rl_data (est_rl e1)) HS' ST' HB' ltac:(lia)).
        cbv zeta in IH. fold rest in IH.
        cps_destruct IH as (d2 & s2 & RES & Q1 & Q2 & Q3).
        * cbn [length] in LF. lia.
        * exact DI2.
        * exact RO2.
        * exists pad. split; [exact PAD|]. rewrite AB2. subst tailw. rewrite (lastcc_any rest (cc_after e1) 0 NE). reflexivity.
        * rewrite F2, e_cc_next. reflexivity.
        * lia.
        * subst s1'. cbn [s_out]. rewrite CF1, OUT, rev_app_distr. reflexivity.
        * subst s1'. cbn [s_avail_out]. rewrite CF2, length_app, rl_pend_next. lia.
        * exists d2, s2. split; [exact RES|]. split; [exact Q1|].
          rewrite rl_pend_next in Q2, Q3. rewrite Q2, Q3. subst s1'. cbn [s_avail_out]. rewrite CF2, !length_app.
          split; [| lia]. f_equal. rewrite <- FI at 1. rewrite (app_assoc (rl_pend (est_rl s))), <- D1, <- !app_assoc. reflexivity.
    - (* [comment removed for export] *)
      assert (LST : last = true) by (destruct last; [reflexivity| exfalso; cps_destruct (EFF eq_refl) as (_ & GE & _); bz_params; lia]).
      subst last. destruct (EFT eq_refl) as [-> _].
      assert (NZ : e_nblock e1 = 0) by (pose proof (R_nneg _ D3) as X; rewrite rl_nblock_est_rl in X; lia).
      pose proof (R_empty _ D3 ltac:(rewrite rl_nblock_est_rl; exact NZ)) as DE.
      rewrite DE, (D2 eq_refl) in D1. cbn [app length] in D1. rewrite Nat.sub_0_r, firstn_all in D1.
      assert (PE : rl_pend (est_rl s) = [] /\ inp = []) by (destruct (rl_pend (est_rl s)); [split; [reflexivity| exact (eq_sym D1)]| discriminate]).
      destruct PE as [PE ->]. rewrite PE in *. cbn [app length Z.of_nat] in *.
      unfold blk_ws' in AB. replace (0 <? e_nblock e1) with false in AB by (symmetry; apply Z.ltb_ge; lia). cbn [app] in AB.
      assert (CA : cc_after e1 = e_combinedCRC s) by (unfold cc_after; replace (0 <? e_nblock e1) with false by (symmetry; apply Z.ltb_ge; lia); exact Kcc).
      rewrite CA in AB.
      cps_destruct (dec_eos (e_combinedCRC s) L d st (Bits pad 0) CCR RO POK AB) as (k2 & d3 & s3 & kb2 & RUN2 & COST2 & CF5 & SCC & CCC2 & RO3 & AB3).
      cps_pose (consumed_fields kb2 st s3 CF5) as (CG1 & CG2 & CG3 & CG4).
      assert (K2 : (k2 <= F)%nat).
      { pose proof (dcost_bound d st d3 s3 RO ltac:(rewrite AB3; cbn; lia) CG4). lia. }
      rewrite (drun_enough k2 F 14 L d st _ RUN2 K2 I). cbn [dwrap]. unfold bzd_cont. rewrite Z.eqb_refl.
      cps_pose (d_fields_sv d3 L) as (_ & _ & J3 & J4 & _). rewrite J3, J4, CCC2, CC, SCC, Z.eqb_refl.
      exists (d_set_sv d3 L), s3. split; [reflexivity|]. split; [rewrite J3, J4, CCC2, CC, SCC; reflexivity|].
      rewrite CG1, CG2, OUT, app_nil_r. split; [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma run_chain : forall m s inp k bp, SI s -> START s inp -> bytes inp -> (length inp < m)%nat ->
    e_blockNo s = k -> bw_numZ (e_bw s) = 0 -> (1 < k -> bw_buff (e_bw s) = bw_buff bp /\ bw_live (e_bw s) = bw_live bp) ->
    CHAIN k bp (enc_run m s inp).
  Proof.
    induction m as [|m IH]; intros s inp k bp HS ST HB LN HK NZ CB; [lia|]. cbn [enc_run].
    pose proof (SI_entry s inp HS ST HB) as SE. pose proof (run_step s inp HS ST HB) as RS. pose proof (enc_entry_keep s inp) as EK.
    pose proof (EXIT_entry s inp ST) as EX.
    destruct (enc_entry s inp) as [[e1 inp'] last]. destruct SE as [SEB _]. cps_destruct EK as (Kcc & Kbw & Kno). destruct EX as [EX _].
    cbn [CHAIN]. rewrite Kbw, Kno. split; [exact HK|]. split; [exact SEB|]. split; [exact NZ|]. split; [exact CB|].
    destruct last; [reflexivity|]. cps_destruct (RS eq_refl) as (HS' & ST' & HB' & LT).
    pose proof (enc_next_fields (enc_exit e1 false)) as F. cbv zeta in F. cps_destruct F as (_ & _ & _ & _ & _ & Fno & _ & Fbw & _).
    pose proof (cb_keep e1 false) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & _ & _ & _ & _ & Kno2 & _).
    apply IH; try assumption; [lia| | |].
    - rewrite Fno. unfold enc_exit. cbn [e_blockNo est_set_modes]. rewrite Kno2, Kno, HK. reflexivity.
    - rewrite Fbw. reflexivity.
    - intros _. rewrite Fbw. cbn [bw_buff bw_live]. rewrite e_bw_exit. split; reflexivity.
  Qed.

  Lemma run_count : forall l, Forall (fun x => 1 <= bw_numZ (blk_bw x)) l -> (length l <= length (enc_bytes l))%nat.
  Proof.
    induction l as [|x l IH]; intros H; [cbn; lia|]. apply Forall_cons_iff in H as [H1 H2]. rewrite enc_bytes_cons, length_app.
    unfold blk_bytes. rewrite bw_bytes_length. specialize (IH H2). cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wlen_bhdr : forall crc op, wlen (ws_bhdr_e crc op) = 105.
  Proof. intros. reflexivity. Qed.
  Lemma wlen_eos : forall cc, wlen (ws_eos cc) = 80.
  Proof. intros. reflexivity. Qed.
  Lemma wlen_nonneg : forall ws, wlegal ws -> 0 <= wlen ws.
  Proof. intros ws W. rewrite <- wbits_blen. apply wbits_len. exact W. Qed.
  Lemma b_len_bapp : forall x y, b_len (bapp x y) = b_len x + b_len y. Proof. reflexivity. Qed.
  Lemma b_len_bytes_bits : forall l, b_len (bytes_bits l) = 8 * Z.of_nat (length l). Proof. reflexivity. Qed.
  Lemma b_len_bw_abs : forall b, b_len (bw_abs b) = 8 * bw_numZ b + bw_live b. Proof. reflexivity. Qed.
  Lemma b_len_Bits : forall a b, b_len (Bits a b) = a. Proof. reflexivity. Qed.

  Lemma numZ_nonlast : forall b0 W, bw_clean b0 -> wlegal W -> 105 <= wlen W -> 1 <= bw_numZ (wapp b0 W).
  Proof.
    intros b0 W C0 WL WB. destruct (wapp_abs W b0 WL C0) as [A1 C1].
    pose proof (f_equal b_len A1) as L1. rewrite b_len_bapp, !b_len_bw_abs, wbits_blen in L1.
    cps_destruct C0 as (X1 & X2 & X3 & X4 & X5). cps_destruct C1 as (C1a & C1b & C1c & C1d & C1e). lia.
  Qed.
  Lemma numZ_last : forall b1 cc, bw_clean b1 -> 1 <= bw_numZ (bs_finish BS_FUEL (wapp b1 (ws_eos cc))).
  Proof.
    intros b1 cc C1.
    pose proof (ws_eos_legal cc) as WE. destruct (wapp_abs _ _ WE C1) as [A2 C2].
    cps_destruct (bs_finish_abs _ C2) as (pad & P1 & P2 & P3 & P4).
    pose proof (f_equal b_len P2) as L2. rewrite b_len_bapp, b_len_bytes_bits, A2, b_len_bapp, b_len_bw_abs, wbits_blen, bw_bytes_length, wlen_eos, b_len_Bits in L2.
    cps_pose (finish_facts BS_FUEL (wapp b1 (ws_eos cc))) as (_ & FB & _).
    cps_destruct C1 as (X1 & X2 & X3 & X4 & X5). cps_destruct C2 as (_ & _ & _ & C2d & _). lia.
  Qed.

  Lemma run_numZ : forall m s inp k, SI s -> START s inp -> bytes inp -> (length inp < m)%nat ->
    e_blockNo s = k -> 1 <= k -> bw_numZ (e_bw s) = 0 -> (1 < k -> bw_clean (BW (bw_buff (e_bw s)) (bw_live (e_bw s)) 0 znew)) ->
    Forall (fun x => 1 <= bw_numZ (blk_bw x)) (enc_run m s inp).
  Proof.
    induction m as [|m IH]; intros s inp k HS ST HB LN HK K1 NZ CL; [lia|]. cbn [enc_run].
    pose proof (SI_entry s inp HS ST HB) as SE. pose proof (run_step s inp HS ST HB) as RS. pose proof (enc_entry_keep s inp) as EK.
    pose proof (enc_entry_facts s inp ST) as EF.
    destruct (enc_entry s inp) as [[e1 inp'] last]. destruct SE as [SEB _]. cps_destruct EK as (Kcc & Kbw & Kno). cps_destruct EF as (_ & _ & _ & _ & _ & EFT & EFF).
    pose proof (compressBlock_wapp e1 last SEB ltac:(rewrite Kbw; exact NZ)) as CW. cbv zeta in CW. rewrite Kbw, Kno, HK in CW.
    set (b0 := if k =? 1 then BW 0 0 0 znew else BW (bw_buff (e_bw s)) (bw_live (e_bw s)) 0 znew) in CW.
    assert (C0 : bw_clean b0) by (subst b0; destruct (Z.eqb_spec k 1); [apply bw_clean_zero| apply CL; lia]).
    pose proof (blk_ws_legal e1 SEB) as WL. destruct (wapp_abs (blk_ws e1) b0 WL C0) as [A1 C1].
    constructor.
    - cbn [fst snd]. rewrite CW. destruct last; [apply numZ_last; exact C1|].
      cps_destruct (EFF eq_refl) as (_ & GE & _).
      assert (NBP : 0 < e_nblock e1) by (bz_params; pose proof BS_range; lia).
      apply numZ_nonlast; [exact C0| exact WL|].
      unfold blk_ws. replace (0 <? e_nblock e1) with true by (symmetry; apply Z.ltb_lt; exact NBP).
      rewrite !wlen_app, wlen_bhdr. pose proof (wlen_nonneg _ (proj2 (BODY e1 (SEB NBP) NBP))).
      assert (0 <= wlen (if e_blockNo e1 =? 1 then ws_stream_hdr BLOCKSIZE100K else [])) by (destruct (e_blockNo e1 =? 1); [apply wlen_nonneg; apply ws_stream_hdr_legal; apply BS_range| cbn; lia]).
      lia.
    - destruct last; [constructor|]. cps_destruct (RS eq_refl) as (HS' & ST' & HB' & LT).
      pose proof (enc_next_fields (enc_exit e1 false)) as F. cbv zeta in F. cps_destruct F as (_ & _ & _ & _ & _ & Fno & _ & Fbw & _).
      pose proof (cb_keep e1 false) as K. cbv zeta in K. cps_destruct K as (_ & _ & _ & _ & _ & _ & _ & Kno2 & _).
      apply (IH _ _ (k + 1)); try assumption; [lia| | lia| |].
      + rewrite Fno. unfold enc_exit. cbn [e_blockNo est_set_modes]. rewrite Kno2, Kno, HK. reflexivity.
      + rewrite Fbw. reflexivity.
      + intros _. rewrite Fbw. cbn [bw_buff bw_live]. rewrite e_bw_exit, CW. apply bw_clean_reset. exact C1.
  Qed.

  (* [comment removed for export] *)
  Definition rl_pot (r : rlst) : Z := 4 * rl_nblock r + 5 * rl_len r.
  Lemma add_pair_pot : forall r, rl_ok r -> 1 <= rl_len r ->
    4 * rl_nblock (add_pair_to_block r) <= 4 * rl_nblock r + 5 * rl_len r.
  Proof.
    intros r OK Hl. unfold add_pair_to_block.
    destruct (Z.eqb_spec (rl_len r) 1) as [E1|N1]; [cbn -[Z.mul Z.add]; lia|].
    destruct (Z.eqb_spec (rl_len r) 2) as [E2|N2]; [cbn -[Z.mul Z.add]; lia|].
    destruct (Z.eqb_spec (rl_len r) 3) as [E3|N3]; [cbn -[Z.mul Z.add]; lia|].
    cbn -[Z.mul Z.add]. lia.
  Qed.
  Lemma add_char_pot : forall r c, rl_inv r -> 0 <= c < 256 -> rl_pot (add_char_to_block r c) <= rl_pot r + 5.
  Proof.
    intros r c [OK P] Hc. cps_pose OK as (A & B & C & D & E). unfold add_char_to_block, rl_pot.
    destruct (negb (c =? rl_ch r) && (rl_len r =? 1)) eqn:K1.
    - apply andb_prop in K1. destruct K1 as [_ K1b]. apply Z.eqb_eq in K1b. cbn -[Z.mul Z.add]. lia.
    - destruct (negb (c =? rl_ch r) || (rl_len r =? 255)) eqn:K2.
      + destruct (Z.ltb_spec (rl_ch r) 256) as [L|L].
        * assert (Hl : 1 <= rl_len r) by (apply P; exact L).
          pose proof (add_pair_pot r OK Hl) as X. cbn [rl_nblock rl_len]. lia.
        * cbn [rl_nblock rl_len]. lia.
      + cbn -[Z.mul Z.add]. lia.
  Qed.
  Lemma rle_fill_pot : forall fuel r inp, RLI r -> bytes inp -> (rl_ch r = 256 -> rl_nblock r = 0) ->
    let '(r', inp') := rle_fill fuel r inp in rl_pot r' <= rl_pot r + 5 * Z.of_nat (length inp - length inp').
  Proof.
    induction fuel as [|f IH]; intros r inp HR HB HE; cbn [rle_fill].
    - rewrite Nat.sub_diag. cbn. lia.
    - destruct (NBLOCKMAX <=? rl_nblock r). { rewrite Nat.sub_diag. cbn. lia. }
      destruct inp as [|c rest]. { cbn. lia. }
      apply Forall_cons_iff in HB as [Hc HB]. cps_destruct (R1 r c HR Hc HE) as (HR' & _ & CH).
      pose proof (add_char_pot r c (RLI_inv r HR) Hc) as P1.
      specialize (IH (add_char_to_block r c) rest HR' HB ltac:(intros X; rewrite CH in X; lia)).
      cps_pose (rle_fill_suffix f (add_char_to_block r c) rest) as (k & SK & LK).
      destruct (rle_fill f (add_char_to_block r c) rest) as [r' inp']. cbn [snd] in SK.
      assert (LI : (length inp' <= length rest)%nat) by (rewrite SK, length_skipn; lia).
      cbn [length]. replace (S (length rest) - length inp')%nat with (S (length rest - length inp')) by lia. lia.
  Qed.

  Lemma run_length : forall m s inp, SI s -> START s inp -> bytes inp -> (length inp < m)%nat ->
    (Z.of_nat (length (enc_run m s inp)) - 1) * (4 * NBLOCKMAX - 1275) <= 5 * Z.of_nat (length inp).
  Proof.
    induction m as [|m IH]; intros s inp HS ST HB LN; [lia|]. cbn [enc_run].
    pose proof (run_step s inp HS ST HB) as RS. pose proof (enc_entry_facts s inp ST) as EF.
    pose proof (RLI_inv _ (SI_rl s HS)) as RI. cps_pose ST as (_ & _ & _ & NB & _).
    assert (POT : let '(e1, inp', last) := enc_entry s inp in last = false -> 4 * NBLOCKMAX - 1275 <= 5 * Z.of_nat (length inp - length inp')).
    { unfold enc_entry. pose proof (rle_fill_pot (S (length inp)) (est_rl s) inp (SI_rl s HS) HB ltac:(intros _; rewrite rl_nblock_est_rl; exact NB)) as P.
      pose proof (rle_fill_stop (S (length inp)) (est_rl s) inp ltac:(lia)) as STP.
      pose proof (rle_fill_data (S (length inp)) (est_rl s) inp (SI_rl s HS) HB ltac:(intros _; rewrite rl_nblock_est_rl; exact NB)) as D.
      destruct (rle_fill _ (est_rl s) inp) as [r' [|c rest]]; [intros; discriminate|]. intros _.
      destruct STP as [STP|STP]; [discriminate|]. destruct D as (D1 & _). pose proof (RLI_inv _ D1) as [(_ & _ & LEN & _) _].
      unfold rl_pot in P. rewrite rl_nblock_est_rl, NB in P. cbn [rl_len est_rl] in P. destruct RI as [(_ & _ & LEN0 & _) _]. cbn [rl_len est_rl] in LEN0. lia. }
    destruct (enc_entry s inp) as [[e1 inp'] last]. cps_destruct EF as (_ & _ & _ & _ & LE & _).
    destruct last.
    - cbn [length]. lia.
    - cps_destruct (RS eq_refl) as (HS' & ST' & HB' & LT). specialize (POT eq_refl). specialize (IH _ _ HS' ST' HB' ltac:(lia)).
      cbn [length]. rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_sub in POT by lia. lia.
  Qed.

  Lemma run_fuel : forall s payload destLen, SI s -> START s payload -> bytes payload ->
    (length (enc_run (S (length payload)) s payload) + 2 <= hc_fuel (z_b2b payload destLen))%nat.
  Proof.
    intros s payload destLen HS ST HB. pose proof (run_length (S (length payload)) s payload HS ST HB ltac:(lia)) as RL.
    unfold hc_fuel, z_b2b. cbn [z_avail_in]. unfold BZ_MAX_UNUSED.
    set (m := Z.of_nat (length (enc_run (S (length payload)) s payload))) in *. set (n := Z.of_nat (length payload)) in *.
    pose proof BS_range as BR.
    assert (A3 : 3 * NBLOCKMAX <= 4 * NBLOCKMAX - 1275) by (bz_params; lia).
    assert (NP : 0 < NBLOCKMAX) by (bz_params; lia).
    assert (M1 : (m - 1) * (3 * NBLOCKMAX) <= 5 * n) by nia.
    pose proof (Z.div_mod n NBLOCKMAX ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n NBLOCKMAX ltac:(lia)) as MB.
    set (q := n / NBLOCKMAX) in *.
    assert (M2 : m - 1 <= 2 * q + 2) by nia.
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition E0OK' (e0 : est) : Prop :=
    E0OK e0 /\ e_blockNo e0 = 1 /\ bw_numZ (e_bw e0) = 0 /\ e_combinedCRC e0 = 0 /\ e_state_in_ch e0 = 256.

  Lemma rd_abs_init : forall junk sv small src dl, rd_abs (d_set_sv (dst_init junk 0 small) sv) (dstrm_init src dl) = bytes_bits src.
  Proof. intros. destruct junk. unfold rd_abs, bytes_bits. cbn -[Z.mul Z.of_nat bytes_val]. reflexivity. Qed.
  Lemma rd_ok_init : forall junk sv small src dl, bytes_ok src -> rd_ok (d_set_sv (dst_init junk 0 small) sv) (dstrm_init src dl).
  Proof. intros. destruct junk. unfold rd_ok. cbn -[bytes_ok]. repeat split; try lia. assumption. Qed.

  Theorem run_numZ0 : forall e0 payload, E0OK' e0 -> SI (e_fin e0 (Z.of_nat (length payload))) -> bytes payload ->
    Forall (fun x => 1 <= bw_numZ (blk_bw x)) (enc_blocks e0 payload).
  Proof.
    (intros e0 payload; cps_intros (OK & BN1 & NZ0 & CC0 & CH0); intros HSI HB). unfold enc_blocks.
    apply (run_numZ _ _ _ 1); try assumption; try lia. apply START_fin. exact OK.
  Qed.

  (* [comment removed for export] *)
  Theorem b2b_roundtrip_junk : forall junk e0 payload dl,
    E0OK' e0 -> SI (e_fin e0 (Z.of_nat (length payload))) -> bytes payload ->
    Z.of_nat (length payload) <= dl ->
    let '(r, n, out, _) := buffToBuffDecompress junk (enc_stream e0 payload) dl (if sm then 1 else 0) in
    (r, n, out) = (BZ_OK, Z.of_nat (length payload), payload).
  Proof.
    intros junk0 e0 payload dl OK' HSI HB DL.
    destruct junk0 as [j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16 j17 j18 j19 j20 j21 j22 j23 j24 j25 j26 j27 j28 j29 j30 j31 j32 j33 j34 j35 j36 j37 j38 j39 j40 j41 j42 j43 j44].
    match goal with |- context [buffToBuffDecompress ?j _ _ _] => set (junk := j) end. pose proof (run_numZ0 e0 payload OK' HSI HB) as NZ. cps_destruct OK' as (OK & BN1 & NZ0 & CC0 & CH0).
    pose proof (START_fin e0 payload OK) as ST0.
    set (s0 := e_fin e0 (Z.of_nat (length payload))) in *.
    assert (RCH : CHAIN 1 (e_bw s0) (enc_blocks e0 payload)).
    { unfold enc_blocks. fold s0. apply run_chain; try assumption; lia. }
    set (l := enc_blocks e0 payload) in *.
    cps_destruct (chain_bits l 1 (e_bw s0) RCH ltac:(lia) ltac:(intros; lia)) as (pad & PAD & BITS & BOK). cbv zeta in BITS. rewrite Z.eqb_refl, bapp_bnil_l in BITS.
    assert (NE : exists e1 last l', l = (e1, last) :: l') by (destruct l as [|[e1 last] l']; [destruct RCH| do 3 eexists; reflexivity]).
    cps_destruct NE as (e1 & last & l' & EL).
    rewrite EL in BITS. rewrite (ws_all_head e1 last l' (e_bw s0)) in BITS by (rewrite <- EL; exact RCH). rewrite <- EL in BITS.
    unfold enc_stream. fold l.
    pose proof (run_count l NZ) as CNT.
    (* [comment removed for export] *)
    unfold buffToBuffDecompress, bzDecompress. cbv zeta.
    set (src := enc_bytes l) in *. set (small := if sm then 1 else 0).
    set (D0 := dst_init junk 0 small). set (S0 := dstrm_init src dl).
    assert (ST10 : d_state D0 = BZ_X_MAGIC_1) by reflexivity.
    rewrite (bzd_loop_first _ D0 S0 ST10), (decompress_first D0 S0 ST10).
    set (D0' := d_set_sv D0 dsv_zero).
    pose proof (rd_ok_init junk dsv_zero small src dl BOK) as RO0. fold D0 D0' S0 in RO0.
    pose proof (rd_abs_init junk dsv_zero small src dl) as AB0. fold D0 D0' S0 in AB0. rewrite BITS, <- app_assoc in AB0.
    assert (WL1 : wlegal (ws_stream_hdr BLOCKSIZE100K)) by (apply ws_stream_hdr_legal; apply BS_range).
    assert (WL2 : wlegal (ws_all' l ++ ws_eos (lastcc 0 l))).
    { apply wlegal_app. split; [| apply ws_eos_legal]. subst l. unfold enc_blocks. fold s0. apply run_legal; assumption. }
    rewrite (wbits_app _ _ WL1 WL2), bapp_assoc in AB0 by (try apply wbits_len; try assumption; cbn; lia).
    assert (BOK2 : bits_ok (bapp (wbits (ws_all' l ++ ws_eos (lastcc 0 l))) (Bits pad 0))) by (apply bapp_ok; [apply wbits_ok; exact WL2| apply pad_ok; exact PAD]).
    cps_destruct (drun_feed (ws_stream_hdr BLOCKSIZE100K) 10 dsv_zero D0' S0 _ _ WL1 RO0 BOK2 AB0 (seg_stream_hdr BLOCKSIZE100K dsv_zero D0' S0 BS_range))
      as (k0 & B & V & s1 & kb0 & RUN0 & REST0 & CF0).
    match type of RUN0 with forall f, _ = dgo f (dres_map2 _ _ (DGo 14 dsv_zero ?dd S0)) => set (D14 := dd) in RUN0 end.
    cps_destruct (REST0 D14) as (AB1 & RO1 & COST1).
    cps_pose (consumed_fields kb0 S0 s1 CF0) as (CG1 & CG2 & CG3 & CG4).
    assert (K0 : (k0 <= 9 * length (s_in S0) + 64)%nat).
    { pose proof (dcost_bound D0' S0 (setLB D14 B V) s1 RO0 ltac:(rewrite AB1; exact (proj1 BOK2)) CG4) as H. change (d_bsLive D0') with 0 in H. lia. }
    change BZ_X_MAGIC_1 with 10.
    replace (9 * length (s_in S0) + 64)%nat with (k0 + (9 * length (s_in S0) + 64 - k0))%nat by lia. rewrite RUN0. cbn [dres_map2 dgo]. unfold FLB.
    cps_destruct (dec_core (S (length payload)) (S (length (s_in S0))) s0 payload (9 * length (s_in S0) + 64 - k0)%nat dsv_zero (setLB D14 B V) s1 []
                HSI ST0 HB ltac:(lia)) as (d2 & s2 & RES & Q1 & Q2 & Q3).
    - change (enc_run (S (length payload)) s0 payload) with l. change (s_in S0) with src. lia.
    - unfold DINV, smallb. rewrite lbg_bs100k, lbg_small. subst D14. split.
      + destruct (smallb D0'); reflexivity.
      + subst D0' D0 small junk. destruct sm; cbn; destruct (smallb _); reflexivity.
    - exact RO1.
    - exists pad. split; [exact PAD|]. fold l. exact AB1.
    - rewrite lbg_cccrc. subst D14 s0. unfold e_fin. cbn [e_combinedCRC est_set_modes]. rewrite CC0. destruct (smallb D0'); reflexivity.
    - rewrite lbg_bsLive. unfold dcost in COST1. rewrite AB1 in COST1. unfold rd_abs in COST1 at 1. cbn [b_len] in COST1.
      destruct RO1 as (R1' & _). rewrite lbg_bsLive in R1'. destruct RO0 as (R0' & _).
      assert (d_bsLive D0' = 0) by reflexivity.
      pose proof (wbits_len _ WL2). unfold bapp in COST1. cbn [b_len] in COST1.
      pose proof (f_equal b_len AB1) as LB1. unfold rd_abs, bapp in LB1. cbn [b_len] in LB1. rewrite lbg_bsLive in LB1. lia.
    - rewrite CG1. reflexivity.
    - rewrite CG2. subst s0. unfold rl_pend, e_fin. cbn [est_rl rl_ch rl_len est_set_modes e_state_in_ch e_state_in_len]. rewrite CH0. cbn. exact DL.
    - fold l in RES. rewrite RES. change (BZ_STREAM_END =? BZ_OK) with false. rewrite Z.eqb_refl. cbv iota.
      rewrite Q3, CG2. unfold s_output. rewrite Q2. subst s0. unfold rl_pend, e_fin in *. cbn [est_rl rl_ch rl_len est_set_modes e_state_in_ch e_state_in_len app] in *.
      rewrite CH0. cbn [Z.ltb andb app length]. rewrite rev_involutive. f_equal. f_equal. subst S0. cbn. lia.
  Qed.

  (* [comment removed for export] *)
End Blocks.

End ACeilS2.
