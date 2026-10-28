(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ.
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
Definition z_b2b (payload : list Z) (destLen : Z) : zstrm :=
  ZS payload (Z.of_nat (length payload)) [] destLen 0 0 0 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma est_set_rl_rl : forall e, est_set_rl e (est_rl e) = e.
Proof. intros e; destruct e; reflexivity. Qed.
Lemma est_rl_set_rl : forall e r, est_rl (est_set_rl e r) = r.
Proof. intros e r; destruct e, r; reflexivity. Qed.
Lemma est_set_rl_set_rl : forall e r r', est_set_rl (est_set_rl e r) r' = est_set_rl e r'.
Proof. intros e r r'; destruct e; reflexivity. Qed.
Lemma est_rl_set_modes : forall e m s x, est_rl (est_set_modes e m s x) = est_rl e.
Proof. intros; destruct e; reflexivity. Qed.
Lemma est_set_modes_set_rl : forall e r m s x, est_set_modes (est_set_rl e r) m s x = est_set_rl (est_set_modes e m s x) r.
Proof. intros; destruct e; reflexivity. Qed.
Lemma est_set_modes_modes : forall e m s x m' s' x', est_set_modes (est_set_modes e m s x) m' s' x' = est_set_modes e m' s' x'.
Proof. intros; destruct e; reflexivity. Qed.
Lemma est_set_modes_id : forall e, est_set_modes e (e_mode e) (e_state e) (e_avail_in_expect e) = e.
Proof. intros e; destruct e; reflexivity. Qed.
Lemma est_set_outpos_id : forall e, est_set_outpos e (e_state_out_pos e) = e.
Proof. intros e; destruct e; reflexivity. Qed.
Lemma est_set_outpos_outpos : forall e p q, est_set_outpos (est_set_outpos e p) q = est_set_outpos e q.
Proof. intros; destruct e; reflexivity. Qed.
Lemma e_mode_set_rl : forall e r, e_mode (est_set_rl e r) = e_mode e. Proof. intros; destruct e; reflexivity. Qed.
Lemma e_state_set_rl : forall e r, e_state (est_set_rl e r) = e_state e. Proof. intros; destruct e; reflexivity. Qed.
Lemma e_aie_set_rl : forall e r, e_avail_in_expect (est_set_rl e r) = e_avail_in_expect e. Proof. intros; destruct e; reflexivity. Qed.
Lemma e_nblock_set_rl : forall e r, e_nblock (est_set_rl e r) = rl_nblock r. Proof. intros; destruct e; reflexivity. Qed.
Lemma e_mode_set_modes : forall e m s x, e_mode (est_set_modes e m s x) = m. Proof. reflexivity. Qed.
Lemma e_state_set_modes : forall e m s x, e_state (est_set_modes e m s x) = s. Proof. reflexivity. Qed.
Lemma e_aie_set_modes : forall e m s x, e_avail_in_expect (est_set_modes e m s x) = x. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma rl_nblock_est_rl : forall e, rl_nblock (est_rl e) = e_nblock e. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint incn (k : nat) (lh : Z * Z) : Z * Z :=
  match k with O => lh | S k' => incn k' (inc64 (fst lh) (snd lh)) end.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint rle_fill (fuel : nat) (r : rlst) (inp : list Z) : rlst * list Z :=
  match fuel with
  | O => (r, inp)
  | S f => if NBLOCKMAX <=? rl_nblock r then (r, inp) else
           match inp with
           | [] => (r, inp)
           | c :: rest => rle_fill f (add_char_to_block r c) rest
           end
  end.

Lemma rle_fill_suffix : forall fuel r inp, exists k, snd (rle_fill fuel r inp) = skipn k inp /\ (k <= length inp)%nat.
Proof.
  induction fuel as [|f IH]; intros r inp; cbn [rle_fill].
  - exists 0%nat. split; [reflexivity| lia].
  - destruct (NBLOCKMAX <=? rl_nblock r); [exists 0%nat; split; [reflexivity| lia]|].
    destruct inp as [|c rest]; [exists 0%nat; split; [reflexivity| cbn; lia]|].
    cps_destruct (IH (add_char_to_block r c) rest) as (k & E & L). exists (S k). cbn. split; [exact E| lia].
Qed.

(* [comment removed for export] *)
Lemma rle_fill_stop : forall fuel r inp, (length inp < fuel)%nat ->
  let '(r', inp') := rle_fill fuel r inp in inp' = [] \/ NBLOCKMAX <= rl_nblock r'.
Proof.
  induction fuel as [|f IH]; intros r inp Hf; [lia|]. cbn [rle_fill].
  destruct (Z.leb_spec NBLOCKMAX (rl_nblock r)) as [L|L]; [right; exact L|].
  destruct inp as [|c rest]; [left; reflexivity|]. apply IH. cbn in Hf. lia.
Qed.

(* [comment removed for export] *)
Definition ci_lift (e : est) (z : zstrm) (r' : rlst) (inp' : list Z) : est * zstrm :=
  let k := (length (z_in z) - length inp')%nat in
  let '(lo, hi) := incn k (z_tin_lo z, z_tin_hi z) in
  (est_set_rl (est_set_modes e (e_mode e) (e_state e) (e_avail_in_expect e - Z.of_nat k)) r',
   ZS inp' (z_avail_in z - Z.of_nat k) (z_outr z) (z_avail_out z) lo hi (z_tout_lo z) (z_tout_hi z)).

Lemma ci_lift_refl : forall e z p, z_avail_in z = Z.of_nat (length (z_in z)) ->
  (let '(e', z') := ci_lift e z (est_rl e) (z_in z) in (e', z', p || negb (Z.of_nat (length (z_in z)) =? Z.of_nat (length (z_in z))))) = (e, z, p).
Proof.
  intros e z p HA. unfold ci_lift. rewrite Nat.sub_diag. cbn [incn fst snd]. rewrite Z.sub_0_r, Z.eqb_refl, Bool.orb_false_r.
  rewrite est_set_modes_id, est_set_rl_rl. change (Z.of_nat 0) with 0. rewrite Z.sub_0_r. destruct z; reflexivity.
Qed.

Theorem copy_input_fill : forall fuel e z p,
  e_mode e <> BZ_M_RUNNING -> z_avail_in z = Z.of_nat (length (z_in z)) -> e_avail_in_expect e = Z.of_nat (length (z_in z)) ->
  copy_input fuel e z p =
    let '(r', inp') := rle_fill fuel (est_rl e) (z_in z) in
    let '(e', z') := ci_lift e z r' inp' in
    (e', z', p || negb (Z.of_nat (length inp') =? Z.of_nat (length (z_in z)))).
Proof.
  induction fuel as [|f IH]; intros e z p HM HA HE.
  - cbn [copy_input rle_fill]. symmetry. apply ci_lift_refl. exact HA.
  - cbn [copy_input rle_fill]. rewrite rl_nblock_est_rl.
    destruct (NBLOCKMAX <=? e_nblock e). { symmetry. apply ci_lift_refl. exact HA. }
    destruct (z_in z) as [|c rest] eqn:ZI.
    { cbn [length Z.of_nat] in HA. rewrite HA. cbn [Z.eqb]. rewrite <- ZI. symmetry. apply ci_lift_refl. rewrite ZI. exact HA. }
    replace (z_avail_in z =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite HA; cbn; lia).
    replace (e_mode e =? BZ_M_RUNNING) with false by (symmetry; apply Z.eqb_neq; exact HM).
    replace (e_avail_in_expect e =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite HE; cbn; lia).
    unfold ci_step. rewrite ZI. cbn [inc64].
    set (e1 := est_set_modes (est_set_rl e (add_char_to_block (est_rl e) c)) _ _ _).
    rewrite (IH e1); subst e1.
    2:{ rewrite e_mode_set_modes, e_mode_set_rl. exact HM. }
    2:{ cbn [z_avail_in z_in]. rewrite HA. cbn [length]. lia. }
    2:{ rewrite e_aie_set_modes, e_aie_set_rl, HE. cbn [z_in length]. lia. }
    rewrite est_rl_set_modes, est_rl_set_rl. cbn [z_in].
    destruct (rle_fill f (add_char_to_block (est_rl e) c) rest) as [r' inp'] eqn:RF.
    cps_pose (rle_fill_suffix f (add_char_to_block (est_rl e) c) rest) as (k & SK & LK). rewrite RF in SK. cbn [snd] in SK.
    assert (LI : (length inp' <= length rest)%nat) by (rewrite SK, length_skipn; lia).
    unfold ci_lift. rewrite ZI. cbn [z_in z_tin_lo z_tin_hi z_avail_in z_outr z_avail_out z_tout_lo z_tout_hi length].
    replace (S (length rest) - length inp')%nat with (S (length rest - length inp')) by lia.
    cbn [incn fst snd].
    destruct (incn (length rest - length inp') _) as [lo hi]. cbn [fst snd].
    rewrite e_mode_set_modes, e_state_set_modes, e_aie_set_modes, e_mode_set_rl, e_state_set_rl, e_aie_set_rl.
    rewrite !est_set_modes_set_rl, est_set_rl_set_rl, est_set_modes_modes.
    f_equal; [f_equal; [f_equal; f_equal; lia| f_equal; lia]|].
    destruct p; [reflexivity|]. cbn [orb].
    destruct (Z.eqb_spec (Z.of_nat (length inp')) (Z.of_nat (S (length rest)))); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition co_lift (e : est) (z : zstrm) (k : nat) : est * zstrm :=
  let '(lo, hi) := incn k (z_tout_lo z, z_tout_hi z) in
  (est_set_outpos e (e_state_out_pos e + Z.of_nat k),
   ZS (z_in z) (z_avail_in z) (rev (zarr_to_list (bw_zb (e_bw e)) (e_state_out_pos e) k) ++ z_outr z) (z_avail_out z - Z.of_nat k)
      (z_tin_lo z) (z_tin_hi z) lo hi).

Lemma e_bw_set_outpos : forall e p, e_bw (est_set_outpos e p) = e_bw e. Proof. reflexivity. Qed.
Lemma e_outpos_set_outpos : forall e p, e_state_out_pos (est_set_outpos e p) = p. Proof. reflexivity. Qed.

Theorem copy_output_drain : forall fuel e z p,
  0 <= z_avail_out z -> e_state_out_pos e <= bw_numZ (e_bw e) ->
  let k := Z.min (z_avail_out z) (bw_numZ (e_bw e) - e_state_out_pos e) in
  (Z.to_nat k < fuel)%nat ->
  copy_output fuel e z p = (let '(e', z') := co_lift e z (Z.to_nat k) in (e', z', p || (0 <? k))).
Proof.
  induction fuel as [|f IH]; intros e z p HA HP k Hf; [lia|].
  cbn [copy_output].
  destruct (Z.eqb_spec (z_avail_out z) 0) as [A0|A0].
  { replace (Z.to_nat k) with 0%nat by lia. unfold co_lift. cbn [incn fst snd zarr_to_list rev app].
    rewrite Z.add_0_r, Z.sub_0_r, est_set_outpos_id. replace (0 <? k) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.orb_false_r. destruct z; reflexivity. }
  destruct (Z.leb_spec (bw_numZ (e_bw e)) (e_state_out_pos e)) as [B0|B0].
  { replace (Z.to_nat k) with 0%nat by lia. unfold co_lift. cbn [incn fst snd zarr_to_list rev app].
    rewrite Z.add_0_r, Z.sub_0_r, est_set_outpos_id. replace (0 <? k) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.orb_false_r. destruct z; reflexivity. }
  cbn [inc64].
  rewrite IH; rewrite ?e_bw_set_outpos, ?e_outpos_set_outpos; cbn [z_avail_out]; try lia.
  set (k' := Z.min (z_avail_out z - 1) (bw_numZ (e_bw e) - (e_state_out_pos e + 1))).
  assert (Ek : Z.to_nat k = S (Z.to_nat k')) by lia.
  unfold co_lift. rewrite e_bw_set_outpos, e_outpos_set_outpos. cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi].
  rewrite Ek. cbn [incn fst snd zarr_to_list rev]. unfold inc64. cbn [fst snd].
  destruct (incn (Z.to_nat k') _) as [lo hi]. rewrite est_set_outpos_outpos, <- app_assoc. cbn [app].
  replace (0 <? k) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r.
  f_equal. f_equal; [f_equal; lia| f_equal; lia].
Qed.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Arguments inUse_clear _ _ _ : simpl never.
Section ACeilS2. Context {BZP : BzParams}.


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
Definition cc_next (cc bcrc : Z) : Z := Z.lxor (Z.lor ((Z.shiftl cc 1) mod 4294967296) (Z.shiftr cc 31)) bcrc.

Lemma cb_shape : forall e is_last, exists arr1 arr2 ftab op nInUse unseq nMTF mtfFreq sel selMtf len code rfreq lp,
  let b' := e_bw (fst (compressBlock e is_last znew)) in
  fst (compressBlock e is_last znew) =
  EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 arr2
      ftab op (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) nInUse (e_inUse e) unseq
      b' (if 0 <? e_nblock e then crc_final (e_blockCRC e) else e_blockCRC e)
      (if 0 <? e_nblock e then cc_next (e_combinedCRC e) (crc_final (e_blockCRC e)) else e_combinedCRC e) (e_blockNo e) nMTF mtfFreq sel selMtf len code rfreq lp.
Proof.
  intros e is_last. cbv zeta. unfold compressBlock.
  destruct (Z.ltb_spec 0 (e_nblock e)) as [POS|ZERO].
  - match goal with |- context [blockSort ?ee znew] => cps_destruct (blockSort_shape ee znew) as (a1 & a2 & ft & op & BS); destruct (blockSort ee znew) as [[[e1 fs] ms] bu] end.
    cbn [fst] in BS |- *. subst e1.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
         e_rfreq e_len_pack bw_buff bw_live bw_numZ bw_zb est_set_bw].
    match goal with |- context [generateMTFValues ?ee znew] => cps_destruct (gm_shape ee znew) as (ga1 & gni & gus & gwr & gmf & GM); destruct (generateMTFValues ee znew) as [eg yy] end.
    cbn [fst] in GM. subst eg.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
         e_rfreq e_len_pack bw_buff bw_live bw_numZ bw_zb est_set_bw].
    match goal with |- context [sendMTFValues ?ee znew znew znew znew znew znew znew] =>
      cps_destruct (sm_shape ee znew znew znew znew znew znew znew) as (sb & snm & ssel & ssm & sln & scd & srf & slp & SM);
      destruct (sendMTFValues ee znew znew znew znew znew znew znew) as [es sm] end.
    cbn [fst] in SM. subst es.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
         e_rfreq e_len_pack bw_buff bw_live bw_numZ bw_zb est_set_bw fst].
    do 14 eexists. reflexivity.
  - cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code
         e_rfreq e_len_pack bw_buff bw_live bw_numZ bw_zb est_set_bw fst].
    do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cb_keep : forall e b, let e' := fst (compressBlock e b znew) in
  e_mode e' = e_mode e /\ e_state e' = e_state e /\ e_avail_in_expect e' = e_avail_in_expect e /\ e_nblock e' = e_nblock e /\
  e_state_in_ch e' = e_state_in_ch e /\ e_state_in_len e' = e_state_in_len e /\ e_inUse e' = e_inUse e /\
  e_blockNo e' = e_blockNo e /\ e_state_out_pos e' = e_state_out_pos e /\
  e_blockCRC e' = (if 0 <? e_nblock e then crc_final (e_blockCRC e) else e_blockCRC e) /\
  e_combinedCRC e' = (if 0 <? e_nblock e then cc_next (e_combinedCRC e) (crc_final (e_blockCRC e)) else e_combinedCRC e).
Proof.
  intros e b. cbv zeta.
  cps_destruct (cb_shape e b) as (a1 & a2 & ft & op & ni & us & nm & mf & sl & sm & ln & cd & rf & lp & E).
  cbv zeta in E. rewrite E. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enc_entry (e : est) (inp : list Z) : est * list Z * bool :=
  let '(r', inp') := rle_fill (S (length inp)) (est_rl e) inp in
  let e1 := est_set_rl (est_set_modes e (e_mode e) (e_state e) (e_avail_in_expect e - Z.of_nat (length inp - length inp'))) r' in
  match inp' with
  | [] => (est_set_rl e1 (flush_RL r'), inp', true)
  | _ => (e1, inp', false)
  end.
(* [comment removed for export] *)
Definition enc_exit (e1 : est) (last : bool) : est :=
  let e2 := fst (compressBlock e1 last znew) in est_set_modes e2 (e_mode e2) BZ_S_OUTPUT (e_avail_in_expect e2).
(* [comment removed for export] *)
Definition enc_next (e2 : est) : est := let e := prepare_new_block e2 in est_set_modes e (e_mode e) BZ_S_INPUT (e_avail_in_expect e).
(* [comment removed for export] *)
Fixpoint enc_run (fuel : nat) (e : est) (inp : list Z) : list (est * bool) :=
  match fuel with
  | O => []
  | S f => let '(e1, inp', last) := enc_entry e inp in
           (e1, last) :: (if last then [] else enc_run f (enc_next (enc_exit e1 false)) inp')
  end.
Definition blk_bw (x : est * bool) : bw := e_bw (fst (compressBlock (fst x) (snd x) znew)).
Definition blk_bytes (x : est * bool) : list Z := bw_bytes (blk_bw x).
Definition enc_bytes (l : list (est * bool)) : list Z := concat (map blk_bytes l).
(* [comment removed for export] *)
Definition e_fin (e0 : est) (n : Z) : est := est_set_modes e0 BZ_M_FINISHING (e_state e0) n.
Definition enc_blocks (e0 : est) (payload : list Z) : list (est * bool) :=
  enc_run (S (length payload)) (e_fin e0 (Z.of_nat (length payload))) payload.
(* [comment removed for export] *)
Definition enc_stream (e0 : est) (payload : list Z) : list Z := enc_bytes (enc_blocks e0 payload).

(* [comment removed for export] *)
Definition START (e : est) (inp : list Z) : Prop :=
  e_mode e = BZ_M_FINISHING /\ e_state e = BZ_S_INPUT /\ e_avail_in_expect e = Z.of_nat (length inp) /\
  e_nblock e = 0 /\ e_state_out_pos e = 0.

Lemma e_bw_exit : forall e1 last, e_bw (enc_exit e1 last) = blk_bw (e1, last). Proof. reflexivity. Qed.

Lemma enc_entry_facts : forall e inp, START e inp ->
  let '(e1, inp', last) := enc_entry e inp in
  e_mode e1 = BZ_M_FINISHING /\ e_state e1 = BZ_S_INPUT /\ e_avail_in_expect e1 = Z.of_nat (length inp') /\ e_state_out_pos e1 = 0 /\
  (length inp' <= length inp)%nat /\
  (last = true -> inp' = [] /\ isempty_RL (est_rl e1) = true) /\
  (last = false -> inp' <> [] /\ NBLOCKMAX <= e_nblock e1 /\ (length inp' < length inp)%nat).
Proof.
  (intros e inp; cps_intros (M & S & X & NB & OP)). unfold enc_entry.
  pose proof (rle_fill_stop (Datatypes.S (length inp)) (est_rl e) inp ltac:(lia)) as ST.
  cps_pose (rle_fill_suffix (Datatypes.S (length inp)) (est_rl e) inp) as (k & SK & LK).
  destruct (rle_fill _ (est_rl e) inp) as [r' inp'] eqn:RF. cbn [snd] in SK.
  assert (LI : (length inp' = length inp - k)%nat) by (rewrite SK, length_skipn; lia).
  destruct inp' as [|c rest].
  - split; [destruct e; exact M|]. split; [destruct e; exact S|]. split; [destruct e; cbn in *; lia|]. split; [destruct e; exact OP|].
    split; [cbn; lia|]. split; [| intros; discriminate]. intros _. split; [reflexivity|].
    rewrite est_rl_set_rl. unfold flush_RL, init_RL, isempty_RL. cbn [rl_ch rl_len]. reflexivity.
  - split; [destruct e; exact M|]. split; [destruct e; exact S|]. split; [destruct e; cbn -[Z.of_nat] in *; lia|]. split; [destruct e; exact OP|].
    split; [cbn in *; lia|]. split; [intros; discriminate|]. intros _. split; [discriminate|].
    destruct ST as [ST|ST]; [discriminate|]. rewrite e_nblock_set_rl. split; [exact ST|].
    (* [comment removed for export] *)
    destruct k as [|k]; [| cbn in *; lia]. exfalso. cbn [skipn] in SK.
    cbn [rle_fill] in RF. rewrite rl_nblock_est_rl, NB in RF.
    replace (NBLOCKMAX <=? 0) with false in RF by (symmetry; apply Z.leb_gt; bz_params; lia).   (* [comment removed for export] *)
    destruct inp as [|c0 rest0]; [discriminate|].
    cps_pose (rle_fill_suffix (length (c0 :: rest0)) (add_char_to_block (est_rl e) c0) rest0) as (k2 & SK2 & LK2).
    rewrite RF in SK2. cbn [snd] in SK2. rewrite SK2 in SK.
    pose proof (f_equal (@length Z) SK) as LL. rewrite length_skipn in LL. cbn in LL. lia.
Qed.

(* [comment removed for export] *)
Definition z_after_in (z : zstrm) (inp' : list Z) : zstrm :=
  let k := (length (z_in z) - length inp')%nat in
  let '(lo, hi) := incn k (z_tin_lo z, z_tin_hi z) in
  ZS inp' (z_avail_in z - Z.of_nat k) (z_outr z) (z_avail_out z) lo hi (z_tout_lo z) (z_tout_hi z).

(* [comment removed for export] *)
Definition hc_A (e : est) (z : zstrm) (pout : bool) : est * zstrm * bool * bool :=
  if e_state e =? BZ_S_OUTPUT then
    let '(e, z, pout) := copy_output (Z.to_nat (z_avail_out z) + 1)%nat e z pout in
    if e_state_out_pos e <? bw_numZ (e_bw e) then (e, z, pout, true) else
    if (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true) else
    let e := prepare_new_block e in
    let e := est_set_modes e (e_mode e) BZ_S_INPUT (e_avail_in_expect e) in
    if (e_mode e =? BZ_M_FLUSHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true)
    else (e, z, pout, false)
  else (e, z, pout, false).
Definition hc_B (lj : zarr) (e : est) (z : zstrm) (pin pout : bool) : est * zstrm * bool * bool * bool :=
  if e_state e =? BZ_S_INPUT then
    let '(e, z, pin) := copy_input (Z.to_nat (z_avail_in z) + 1)%nat e z pin in
    if negb (e_mode e =? BZ_M_RUNNING) && (e_avail_in_expect e =? 0) then
      let e := est_set_rl e (flush_RL (est_rl e)) in
      let '(e, _) := compressBlock e (e_mode e =? BZ_M_FINISHING) lj in
      (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
    else if NBLOCKMAX <=? e_nblock e then
      let '(e, _) := compressBlock e false lj in
      (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
    else if z_avail_in z =? 0 then (e, z, pin, pout, true)
    else (e, z, pin, pout, false)
  else (e, z, pin, pout, false).
Lemma hc_iter_AB : forall lj e z pin pout,
  hc_iter lj e z pin pout = (let '(e, z, pout, brk) := hc_A e z pout in if brk then (e, z, pin, pout, true) else hc_B lj e z pin pout).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hc_B_input : forall e inp z pin pout, START e inp -> z_in z = inp -> z_avail_in z = Z.of_nat (length inp) ->
  hc_B znew e z pin pout =
    let '(e1, inp', last) := enc_entry e inp in
    (enc_exit e1 last, z_after_in z inp', pin || negb (Z.of_nat (length inp') =? Z.of_nat (length inp)), pout, false).
Proof.
  intros e inp z pin pout ST ZI ZA. cps_pose ST as (M & S & X & NB & OP).
  unfold hc_B. rewrite S, Z.eqb_refl.
  rewrite copy_input_fill; [| rewrite M; discriminate| rewrite ZI; exact ZA| rewrite ZI; exact X].
  unfold enc_entry. rewrite ZI, ZA. replace (Z.to_nat (Z.of_nat (length inp)) + 1)%nat with (Datatypes.S (length inp)) by lia.
  pose proof (rle_fill_stop (Datatypes.S (length inp)) (est_rl e) inp ltac:(lia)) as STP.
  cps_pose (rle_fill_suffix (Datatypes.S (length inp)) (est_rl e) inp) as (k & SK & LK).
  destruct (rle_fill _ (est_rl e) inp) as [r' inp']. cbn [snd] in SK.
  assert (LI : (length inp' <= length inp)%nat) by (rewrite SK, length_skipn; lia).
  unfold ci_lift, z_after_in. rewrite ZI.
  destruct inp' as [|c rest].
  - cbn [length]. rewrite Nat.sub_0_r.
    destruct (incn _ (z_tin_lo z, z_tin_hi z)) as [lo hi]. cbv beta zeta iota.
    rewrite e_mode_set_rl, e_mode_set_modes, e_aie_set_rl, e_aie_set_modes, M, X, Z.sub_diag.
    change (negb (BZ_M_FINISHING =? BZ_M_RUNNING) && (0 =? 0))%bool with true. cbv iota.
    rewrite est_rl_set_rl.
    unfold enc_exit. rewrite !e_mode_set_rl, e_mode_set_modes. change (BZ_M_FINISHING =? BZ_M_FINISHING) with true.
    destruct (compressBlock _ true znew) as [e2 cb]. cbn [fst]. reflexivity.
  - destruct (incn _ (z_tin_lo z, z_tin_hi z)) as [lo hi]. cbv beta zeta iota.
    rewrite e_mode_set_rl, e_mode_set_modes, e_aie_set_rl, e_aie_set_modes, e_nblock_set_rl, M, X.
    replace (Z.of_nat (length inp) - Z.of_nat (length inp - length (c :: rest)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn in *; lia).
    change (negb (BZ_M_FINISHING =? BZ_M_RUNNING) && false)%bool with false. cbv iota.
    destruct STP as [STP|STP]; [discriminate|]. replace (NBLOCKMAX <=? rl_nblock r') with true by (symmetry; apply Z.leb_le; exact STP).
    unfold enc_exit. destruct (compressBlock _ false znew) as [e2 cb]. cbn [fst]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hc_iter_input : forall e inp z pin pout, START e inp -> z_in z = inp -> z_avail_in z = Z.of_nat (length inp) ->
  hc_iter znew e z pin pout =
    let '(e1, inp', last) := enc_entry e inp in
    (enc_exit e1 last, z_after_in z inp', pin || negb (Z.of_nat (length inp') =? Z.of_nat (length inp)), pout, false).
Proof.
  intros e inp z pin pout ST ZI ZA. rewrite hc_iter_AB. unfold hc_A. rewrite (proj1 (proj2 ST)).
  change (BZ_S_INPUT =? BZ_S_OUTPUT) with false. cbv beta zeta iota. apply hc_B_input; assumption.
Qed.

Lemma enc_next_outpos : forall es p,
  (let e := prepare_new_block (est_set_outpos es p) in est_set_modes e (e_mode e) BZ_S_INPUT (e_avail_in_expect e)) = enc_next es.
Proof. intros es p. destruct es; cbv beta iota zeta delta -[prepare_new_block_rl inUse_clear]. reflexivity. Qed.
Lemma isempty_RL_e_eq : forall e, isempty_RL_e e = negb ((e_state_in_ch e <? 256) && (0 <? e_state_in_len e)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hc_A_exit : forall e1 last (inp' : list Z) z pout,
  e_mode e1 = BZ_M_FINISHING -> e_avail_in_expect e1 = Z.of_nat (length inp') -> e_state_out_pos e1 = 0 ->
  (last = true -> inp' = [] /\ isempty_RL (est_rl e1) = true) -> (last = false -> inp' <> []) ->
  0 <= z_avail_out z -> 0 <= bw_numZ (blk_bw (e1, last)) ->
  let es := enc_exit e1 last in let nz := bw_numZ (blk_bw (e1, last)) in
  let k := Z.min (z_avail_out z) nz in
  let zo := snd (co_lift es z (Z.to_nat k)) in
  hc_A es z pout =
    if z_avail_out z <? nz then (est_set_outpos es k, zo, pout || (0 <? k), true)
    else if last then (est_set_outpos es nz, zo, pout || (0 <? k), true)
    else (enc_next es, zo, pout || (0 <? k), false).
Proof.
  intros e1 last inp' z pout M X OP LT LF AO NZ. cbv zeta.
  pose proof (cb_keep e1 last) as K. cbv zeta in K. cps_destruct K as (Km & Ks & Kx & Kn & Kch & Klen & Kiu & Kno & Kop & Kcrc & Kcc).
  unfold hc_A. unfold enc_exit at 1. rewrite e_state_set_modes, Z.eqb_refl. fold (enc_exit e1 last).
  assert (OP' : e_state_out_pos (enc_exit e1 last) = 0) by (unfold enc_exit; cbn [e_state_out_pos est_set_modes]; rewrite Kop; exact OP).
  assert (BW' : e_bw (enc_exit e1 last) = blk_bw (e1, last)) by reflexivity.
  rewrite (copy_output_drain _ (enc_exit e1 last) z pout AO); rewrite ?OP', ?BW'; [| lia| lia].
  rewrite Z.sub_0_r. unfold co_lift. rewrite OP', BW', Z.add_0_l.
  destruct (incn _ (z_tout_lo z, z_tout_hi z)) as [lo hi]. cbv beta zeta iota. cbn [snd].
  rewrite e_outpos_set_outpos, e_bw_set_outpos, BW'. rewrite !Z2Nat.id by lia.
  destruct (Z.ltb_spec (z_avail_out z) (bw_numZ (blk_bw (e1, last)))) as [LTz|GEz].
  - replace (Z.min (z_avail_out z) (bw_numZ (blk_bw (e1, last))) <? bw_numZ (blk_bw (e1, last))) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  - rewrite Z.min_r by lia. rewrite Z.ltb_irrefl.
    assert (Em : e_mode (est_set_outpos (enc_exit e1 last) (bw_numZ (blk_bw (e1, last)))) = BZ_M_FINISHING).
    { unfold enc_exit. cbn [e_mode est_set_outpos est_set_modes]. rewrite Km. exact M. }
    assert (Ex : e_avail_in_expect (est_set_outpos (enc_exit e1 last) (bw_numZ (blk_bw (e1, last)))) = Z.of_nat (length inp')).
    { unfold enc_exit. cbn [e_avail_in_expect est_set_outpos est_set_modes]. rewrite Kx. exact X. }
    assert (Ee : isempty_RL_e (est_set_outpos (enc_exit e1 last) (bw_numZ (blk_bw (e1, last)))) = isempty_RL (est_rl e1)).
    { rewrite isempty_RL_e_eq. unfold enc_exit. cbn [e_state_in_ch e_state_in_len est_set_outpos est_set_modes]. rewrite Kch, Klen. reflexivity. }
    rewrite Em, Ex, Ee, Z.eqb_refl. cbn [andb].
    destruct last.
    + destruct (LT eq_refl) as [-> ->]. cbn [length Z.of_nat Z.eqb]. reflexivity.
    + specialize (LF eq_refl). replace (Z.of_nat (length inp') =? 0) with false by (symmetry; apply Z.eqb_neq; destruct inp'; [congruence| cbn; lia]).
      cbn [andb]. rewrite enc_next_outpos.
      replace (e_mode (enc_next (enc_exit e1 false)) =? BZ_M_FLUSHING) with false; [reflexivity|].
      unfold enc_next, enc_exit. cbn [e_mode est_set_modes prepare_new_block]. rewrite Km, M. reflexivity.
Qed.

Definition EXIT (e1 : est) (last : bool) (inp' : list Z) : Prop :=
  e_mode e1 = BZ_M_FINISHING /\ e_avail_in_expect e1 = Z.of_nat (length inp') /\ e_state_out_pos e1 = 0 /\
  (last = true -> inp' = [] /\ isempty_RL (est_rl e1) = true) /\ (last = false -> inp' <> []).

Lemma EXIT_entry : forall e inp, START e inp -> let '(e1, inp', last) := enc_entry e inp in EXIT e1 last inp' /\ (last = false -> (length inp' < length inp)%nat).
Proof.
  intros e inp ST. pose proof (enc_entry_facts e inp ST) as F. destruct (enc_entry e inp) as [[e1 inp'] last].
  cps_destruct F as (M & S & X & OP & LE & LT & LF). split; [| intros H; exact (proj2 (proj2 (LF H)))].
  split; [exact M|]. split; [exact X|]. split; [exact OP|]. split; [exact LT|]. intros H; exact (proj1 (LF H)).
Qed.

Lemma enc_next_fields : forall e2, let e := enc_next e2 in
  e_mode e = e_mode e2 /\ e_state e = BZ_S_INPUT /\ e_avail_in_expect e = e_avail_in_expect e2 /\ e_nblock e = 0 /\ e_state_out_pos e = 0 /\
  e_blockNo e = e_blockNo e2 + 1 /\ e_combinedCRC e = e_combinedCRC e2 /\ e_bw e = BW (bw_buff (e_bw e2)) (bw_live (e_bw e2)) 0 znew /\
  e_arr1 e = e_arr1 e2 /\ e_arr2 e = e_arr2 e2 /\ e_ftab e = e_ftab e2 /\ e_state_in_ch e = e_state_in_ch e2 /\ e_state_in_len e = e_state_in_len e2 /\
  e_blockCRC e = crc_init /\ e_inUse e = inUse_clear (e_inUse e2) 0 256.
Proof. intros e2. destruct e2; cbv beta iota zeta delta -[inUse_clear]. repeat split; reflexivity. Qed.

Lemma START_next : forall e1 last inp', EXIT e1 last inp' -> START (enc_next (enc_exit e1 last)) inp'.
Proof.
  (intros e1 last inp'; cps_intros (M & X & OP & _ & _)).
  pose proof (enc_next_fields (enc_exit e1 last)) as F. cbv zeta in F. cps_destruct F as (F1 & F2 & F3 & F4 & F5 & _).
  pose proof (cb_keep e1 last) as K. cbv zeta in K. cps_destruct K as (Km & Ks & Kx & _).
  unfold START. rewrite F1, F2, F3, F4, F5. unfold enc_exit. cbn [e_mode e_avail_in_expect est_set_modes]. rewrite Km, Kx, M, X.
  repeat split; reflexivity.
Qed.

Lemma zarr_to_list_firstn : forall a lo n k, (k <= n)%nat -> firstn k (zarr_to_list a lo n) = zarr_to_list a lo k.
Proof.
  intros a lo n. revert lo. induction n as [|n IH]; intros lo k Hk.
  - replace k with 0%nat by lia. reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [zarr_to_list firstn]. rewrite IH by lia. reflexivity.
Qed.
Lemma bw_bytes_length : forall b, length (bw_bytes b) = Z.to_nat (bw_numZ b).
Proof. intros b. unfold bw_bytes. apply zarr_to_list_length. Qed.
Lemma enc_bytes_cons : forall x l, enc_bytes (x :: l) = blk_bytes x ++ enc_bytes l.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hc_loop_sim : forall n f e1 last inp' z pin pout,
  EXIT e1 last inp' -> z_in z = inp' -> z_avail_in z = Z.of_nat (length inp') -> 0 <= z_avail_out z -> (length inp' < n)%nat ->
  let L := if last then [] else enc_run n (enc_next (enc_exit e1 false)) inp' in
  (length L < f)%nat ->
  Forall (fun x => 1 <= bw_numZ (blk_bw x)) ((e1, last) :: L) ->
  let str := blk_bytes (e1, last) ++ enc_bytes L in
  let '(e', z', prog) := hc_loop (S f) znew (enc_exit e1 last) z pin pout in
  z_outr z' = rev (firstn (Z.to_nat (z_avail_out z)) str) ++ z_outr z /\
  z_avail_out z' = z_avail_out z - Z.min (z_avail_out z) (Z.of_nat (length str)) /\
  (pout = true \/ 0 < z_avail_out z -> prog = true) /\ e_mode e' = BZ_M_FINISHING /\
  (Z.of_nat (length str) <= z_avail_out z ->
     e_avail_in_expect e' = 0 /\ isempty_RL_e e' = true /\ e_state_out_pos e' = bw_numZ (e_bw e') /\ z_in z' = [] /\ z_avail_in z' = 0) /\
  (z_avail_out z < Z.of_nat (length str) -> e_state_out_pos e' < bw_numZ (e_bw e')).
Proof.
  induction n as [|n IH]; intros f e1 last inp' z pin pout EX ZI ZA AO LN; [lia|].
  cbv zeta. intros LF NZ.
  cps_pose EX as (M & X & OP & LT & LFa).
  apply Forall_cons_iff in NZ as [NZ1 NZL]. cbn [fst snd] in NZ1.
  pose proof (cb_keep e1 last) as K. cbv zeta in K. cps_destruct K as (Km & Ks & Kx & Kn & Kch & Klen & Kiu & Kno & Kop & Kcrc & Kcc).
  cbn [hc_loop]. rewrite hc_iter_AB.
  rewrite (hc_A_exit e1 last inp' z pout M X OP LT LFa AO ltac:(lia)).
  set (nz := bw_numZ (blk_bw (e1, last))) in *.
  assert (LB : length (blk_bytes (e1, last)) = Z.to_nat nz) by (unfold blk_bytes; apply bw_bytes_length).
  destruct (Z.ltb_spec (z_avail_out z) nz) as [LTz|GEz].
  - (* [comment removed for export] *)
    cbv beta iota. unfold co_lift. cbn [snd].
    destruct (incn _ (z_tout_lo z, z_tout_hi z)) as [lo hi]. cbn [snd z_outr z_avail_out].
    rewrite Z.min_l by lia.
    split. { rewrite firstn_app, LB. replace (Z.to_nat (z_avail_out z) - Z.to_nat nz)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
             unfold blk_bytes, bw_bytes. cbn [fst snd]. fold nz. rewrite zarr_to_list_firstn by lia.
             unfold enc_exit. cbn [e_bw est_set_modes e_state_out_pos]. rewrite Kop, OP. reflexivity. }
    split. { rewrite length_app, LB. rewrite Z.min_l by lia. lia. }
    split. { intros [P|P]; [rewrite P; cbn; rewrite ?Bool.orb_true_r; reflexivity|].
             replace (0 <? z_avail_out z) with true by (symmetry; apply Z.ltb_lt; lia). rewrite !Bool.orb_true_r. reflexivity. }
    split. { cbn [e_mode est_set_outpos enc_exit est_set_modes]. unfold enc_exit. cbn [e_mode est_set_modes]. rewrite Km. exact M. }
    split. { intros C. rewrite length_app, LB in C. lia. }
    intros _. rewrite e_outpos_set_outpos, e_bw_set_outpos, e_bw_exit. fold nz. lia.
  - rewrite Z.min_r by lia.
    destruct last.
    + (* [comment removed for export] *)
      destruct (LT eq_refl) as [-> EM]. cbv beta iota. unfold co_lift. cbn [snd].
      destruct (incn _ (z_tout_lo z, z_tout_hi z)) as [lo hi]. cbn [snd z_outr z_avail_out z_in z_avail_in enc_bytes map concat]. rewrite app_nil_r.
      split. { rewrite firstn_all2 by (rewrite LB; lia). rewrite e_bw_exit. f_equal. f_equal.
               unfold blk_bytes, bw_bytes. cbn [fst snd]. fold nz. f_equal. unfold enc_exit. cbn [e_state_out_pos est_set_modes]. rewrite Kop, OP. reflexivity. }
      split. { rewrite LB. rewrite Z.min_r by lia. lia. }
      split. { intros _. replace (0 <? nz) with true by (symmetry; apply Z.ltb_lt; lia). rewrite !Bool.orb_true_r. reflexivity. }
      split. { cbn [e_mode est_set_outpos]. unfold enc_exit. cbn [e_mode est_set_modes]. rewrite Km. exact M. }
      split. { intros _. rewrite e_outpos_set_outpos, e_bw_set_outpos, e_bw_exit. fold nz.
               unfold enc_exit. cbn [e_avail_in_expect est_set_outpos est_set_modes]. rewrite isempty_RL_e_eq. cbn [e_state_in_ch e_state_in_len est_set_outpos est_set_modes].
               rewrite Kx, Kch, Klen, X, ZI. cbn [length Z.of_nat]. unfold isempty_RL in EM. cbn [rl_ch rl_len est_rl] in EM.
               repeat split; try reflexivity; try exact EM. exact ZA. }
      intros C. rewrite LB in C. lia.
    + (* [comment removed for export] *)
      specialize (LFa eq_refl). cbv beta iota.
      pose proof (START_next e1 false inp' EX) as STn.
      set (es := enc_exit e1 false) in *. set (zo := snd (co_lift es z (Z.to_nat nz))).
      assert (ZO : z_in zo = inp' /\ z_avail_in zo = Z.of_nat (length inp') /\ z_avail_out zo = z_avail_out z - nz /\
                   z_outr zo = rev (blk_bytes (e1, false)) ++ z_outr z).
      { subst zo. unfold co_lift. destruct (incn _ (z_tout_lo z, z_tout_hi z)) as [lo hi]. cbn [snd z_in z_avail_in z_avail_out z_outr].
        split; [exact ZI|]. split; [exact ZA|]. split; [lia|]. unfold blk_bytes, bw_bytes. cbn [fst snd]. subst es. rewrite e_bw_exit. fold nz.
        unfold enc_exit. cbn [e_state_out_pos est_set_modes]. rewrite Kop, OP. reflexivity. }
      cps_destruct ZO as (ZO1 & ZO2 & ZO3 & ZO4).
      rewrite (hc_B_input (enc_next es) inp' zo pin _ STn ZO1 ZO2).
      pose proof (EXIT_entry (enc_next es) inp' STn) as EXn.
      cbn [enc_run] in LF, NZL |- *.
      destruct (enc_entry (enc_next es) inp') as [[e1' inp''] last']. destruct EXn as [EXn LT'].
      assert (LEN'' : (length inp'' <= length inp')%nat /\ (last' = true -> inp'' = [])).
      { cps_destruct EXn as (_ & X' & _ & LT1 & LF1).
        destruct last'; [destruct (LT1 eq_refl) as [-> _]; cbn; split; [lia| reflexivity]| pose proof (LT' eq_refl); split; [lia| discriminate]]. }
      destruct LEN'' as [LEN'' LQ].
      assert (AO' : 0 <= z_avail_out (z_after_in zo inp'')) by (unfold z_after_in; destruct (incn _ _) as [lo hi]; cbn; lia).
      destruct f as [|f]; [cbn [length] in LF; lia|].
      specialize (IH f e1' last' inp'' (z_after_in zo inp'') (pin || negb (Z.of_nat (length inp'') =? Z.of_nat (length inp'))) (pout || (0 <? nz)) EXn).
      cbv zeta in IH.
      assert (ZI' : z_in (z_after_in zo inp'') = inp'') by (unfold z_after_in; destruct (incn _ _); reflexivity).
      assert (ZA' : z_avail_in (z_after_in zo inp'') = Z.of_nat (length inp'')).
      { unfold z_after_in. rewrite ZO1. destruct (incn _ _); cbn [z_avail_in]. rewrite ZO2. lia. }
      assert (ZV' : z_avail_out (z_after_in zo inp'') = z_avail_out z - nz) by (unfold z_after_in; destruct (incn _ _); cbn [z_avail_out]; exact ZO3).
      assert (ZR' : z_outr (z_after_in zo inp'') = rev (blk_bytes (e1, false)) ++ z_outr z) by (unfold z_after_in; destruct (incn _ _); cbn [z_outr]; exact ZO4).
      specialize (IH ZI' ZA' AO').
      assert (LP : (1 <= length inp')%nat) by (destruct inp'; [congruence| cbn; lia]).
      assert (LN' : (length inp'' < n)%nat) by (destruct last'; [rewrite (LQ eq_refl); cbn; lia| pose proof (LT' eq_refl); lia]).
      specialize (IH LN').
      match goal with |- context [hc_loop (Datatypes.S f) znew ?ee ?zz ?pi ?po] =>
        destruct (hc_loop (Datatypes.S f) znew ee zz pi po) as [[e' z'] prog] eqn:HL end.
      assert (LF' : (length (if last' then [] else enc_run n (enc_next (enc_exit e1' false)) inp'') < f)%nat).
      { cbn [length] in LF. destruct last'; cbn [length] in LF |- *; lia. }
      specialize (IH LF' ltac:(constructor; [exact (Forall_inv NZL)| destruct last'; [constructor| exact (Forall_inv_tail NZL)]])).
      rewrite ZV', ZR' in IH. cps_destruct IH as (R1 & R2 & R3 & R4 & R5 & R6).
      rewrite enc_bytes_cons.
      set (str' := blk_bytes (e1', last') ++ enc_bytes (if last' then [] else enc_run n (enc_next (enc_exit e1' false)) inp'')) in *.
      rewrite (length_app (blk_bytes (e1, false)) str'), LB.
      split. { rewrite R1, firstn_app, LB, (firstn_all2 (blk_bytes (e1, false))) by lia. rewrite rev_app_distr, <- app_assoc. f_equal. f_equal. f_equal. lia. }
      split. { rewrite R2. lia. }
      split. { intros _. apply R3. left. replace (0 <? nz) with true by (symmetry; apply Z.ltb_lt; lia). apply Bool.orb_true_r. }
      split. { exact R4. }
      split. { intros C. apply R5. lia. }
      intros C. apply R6. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition E0OK (e0 : est) : Prop :=
  e_mode e0 = BZ_M_RUNNING /\ e_state e0 = BZ_S_INPUT /\ e_nblock e0 = 0 /\ e_state_out_pos e0 = 0.

Lemma START_fin : forall e0 payload, E0OK e0 -> START (e_fin e0 (Z.of_nat (length payload))) payload.
Proof. (intros e0 payload; cps_intros (M & S & NB & OP)). unfold START, e_fin. cbn. rewrite S, NB, OP. repeat split; reflexivity. Qed.

Lemma enc_blocks_eq : forall e0 payload, enc_blocks e0 payload =
  let '(e1, inp', last) := enc_entry (e_fin e0 (Z.of_nat (length payload))) payload in
  (e1, last) :: (if last then [] else enc_run (length payload) (enc_next (enc_exit e1 false)) inp').
Proof. reflexivity. Qed.

Theorem b2b_bzCompress : forall e0 payload destLen,
  E0OK e0 -> 0 < destLen ->
  Forall (fun x => 1 <= bw_numZ (blk_bw x)) (enc_blocks e0 payload) ->
  (length (enc_blocks e0 payload) + 2 <= hc_fuel (z_b2b payload destLen))%nat ->
  let str := enc_stream e0 payload in
  let '(ret, e', z') := bzCompress znew e0 (z_b2b payload destLen) BZ_FINISH in
  (Z.of_nat (length str) <= destLen ->
     ret = BZ_STREAM_END /\ z_outr z' = rev str /\ z_avail_out z' = destLen - Z.of_nat (length str) /\ z_in z' = [] /\ z_avail_in z' = 0) /\
  (destLen < Z.of_nat (length str) ->
     ret = BZ_FINISH_OK /\ z_outr z' = rev (firstn (Z.to_nat destLen) str) /\ z_avail_out z' = 0).
Proof.
  intros e0 payload destLen OK DL NZ FUEL. cbv zeta. cps_pose OK as (M & S & NB & OP).
  unfold bzCompress. rewrite M. change (BZ_M_RUNNING =? BZ_M_RUNNING) with true. cbv iota.
  change (BZ_FINISH =? BZ_RUN) with false. change (BZ_FINISH =? BZ_FLUSH) with false. change (BZ_FINISH =? BZ_FINISH) with true. cbv iota.
  change (BZ_M_FINISHING =? BZ_M_IDLE) with false. change (BZ_M_FINISHING =? BZ_M_RUNNING) with false.
  change (BZ_M_FINISHING =? BZ_M_FLUSHING) with false. cbn [negb]. cbv iota.
  rewrite e_aie_set_modes. cbn [z_avail_in z_b2b]. rewrite Z.eqb_refl. cbn [negb].
  unfold handle_compress.
  destruct (hc_fuel (z_b2b payload destLen)) as [|f0] eqn:HF; [cbn in FUEL; lia|].
  cbn [hc_loop]. fold (e_fin e0 (Z.of_nat (length payload))).
  pose proof (START_fin e0 payload OK) as ST0.
  rewrite (hc_iter_input _ payload _ false false ST0) by reflexivity.
  unfold enc_stream. rewrite enc_blocks_eq in NZ, FUEL |- *.
  pose proof (EXIT_entry _ payload ST0) as EX1.
  destruct (enc_entry (e_fin e0 (Z.of_nat (length payload))) payload) as [[e1 inp'] last]. destruct EX1 as [EX1 LT1].
  cbv beta iota.
  destruct f0 as [|f]; [cbn [length] in FUEL; lia|].
  assert (ZI : z_in (z_after_in (z_b2b payload destLen) inp') = inp') by (unfold z_after_in; destruct (incn _ _); reflexivity).
  assert (ZA : z_avail_in (z_after_in (z_b2b payload destLen) inp') = Z.of_nat (length inp')).
  { unfold z_after_in. cbn [z_in z_b2b z_avail_in]. destruct (incn _ _); cbn [z_avail_in].
    cps_destruct EX1 as (_ & _ & _ & LT & LF). destruct last; [destruct (LT eq_refl) as [-> _]; cbn; lia| pose proof (LT1 eq_refl); lia]. }
  assert (ZV : z_avail_out (z_after_in (z_b2b payload destLen) inp') = destLen) by (unfold z_after_in; destruct (incn _ _); reflexivity).
  assert (ZR : z_outr (z_after_in (z_b2b payload destLen) inp') = []) by (unfold z_after_in; destruct (incn _ _); reflexivity).
  assert (LN : (length inp' < length payload)%nat \/ last = true).
  { destruct last; [right; reflexivity| left; exact (LT1 eq_refl)]. }
  pose proof (hc_loop_sim (if last then Datatypes.S (length inp') else length payload) f e1 last inp' (z_after_in (z_b2b payload destLen) inp')
                (false || negb (Z.of_nat (length inp') =? Z.of_nat (length payload))) false EX1 ZI ZA ltac:(rewrite ZV; lia)
                ltac:(destruct last; lia)) as SIM.
  cbv zeta in SIM. rewrite ZV, ZR in SIM.
  replace (if last then [] else enc_run (if last then Datatypes.S (length inp') else length payload) (enc_next (enc_exit e1 false)) inp')
    with (if last then [] else enc_run (length payload) (enc_next (enc_exit e1 false)) inp') in SIM by (destruct last; reflexivity).
  specialize (SIM ltac:(cbn [length] in FUEL |- *; destruct last; cbn [length] in *; lia) NZ).
  destruct (hc_loop (Datatypes.S f) znew (enc_exit e1 last) _ _ false) as [[e' z'] prog].
  cps_destruct SIM as (R1 & R2 & R3 & R4 & R5 & R6). rewrite (R3 (or_intror DL)). cbn [negb]. cbv iota.
  rewrite app_nil_r in R1. rewrite enc_bytes_cons.
  set (str := blk_bytes (e1, last) ++ enc_bytes (if last then [] else enc_run (length payload) (enc_next (enc_exit e1 false)) inp')) in *.
  destruct (Z.le_gt_cases (Z.of_nat (length str)) destLen) as [FIT|OVF].
  - cps_destruct (R5 FIT) as (X1 & X2 & X3 & X4 & X5). rewrite X1, X2, X3. change (0 <? 0) with false. rewrite Z.ltb_irrefl. cbv beta iota zeta.
    split; [| intros; lia]. intros _.
    split; [reflexivity|]. split; [rewrite R1, firstn_all2 by lia; reflexivity|]. split; [rewrite R2; lia|]. split; assumption.
  - pose proof (R6 OVF) as X. replace (e_state_out_pos e' <? bw_numZ (e_bw e')) with true by (symmetry; apply Z.ltb_lt; exact X).
    rewrite Bool.orb_true_r. cbv beta iota zeta. split; [intros; lia|]. intros _. split; [reflexivity|]. split; [exact R1|]. rewrite R2. lia.
Qed.


End ACeilS2.
