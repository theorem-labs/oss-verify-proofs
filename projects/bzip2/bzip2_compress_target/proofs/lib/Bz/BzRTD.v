(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCStream BzCState BzCHuff BzCMtf BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2Theory.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2D.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR2D1 BzR2D BzR5a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG BzR5cE BzR5cF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cS.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D.BzR2Z OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.BzR5cX OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCRebuildF BzCFactsGm.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR4a BzR4d.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a.BzR4m OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4d.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_rows_frame : forall (F : dst -> Prop) n i g16 bit d,
  (forall x v, F x -> F (d_set_inUse (d_set_state x 29) v)) -> F d -> F (map_rows n i g16 bit d).
Proof.
  intros F n. induction n as [|n IH]; intros i g16 bit d HF Hd; cbn [map_rows]; [exact Hd|].
  apply IH; [exact HF|]. destruct (negb (g16 i =? 0)); [apply HF; exact Hd| exact Hd].
Qed.

Lemma makeMaps_d_eq : forall d, makeMaps_d d = d_set_nInUse (d_set_s2u d (fst (mkmaps 256 0 (d_inUse d) (d_s2u d) 0))) (snd (mkmaps 256 0 (d_inUse d) (d_s2u d) 0)).
Proof. intros d. unfold makeMaps_d. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0). reflexivity. Qed.

Ltac dget := cbn [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0
    d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16
    d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
    d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small
    d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16
    d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u
    d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv
    sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock sv_es sv_N sv_curr
    sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
    sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos sv_set_nextSym
    sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj sv_set_gSel sv_set_gMinlen sv_set_gPtr].

(* [comment removed for export] *)
Definition STATIC (d x : dst) : Prop :=
  d_bs100k x = d_bs100k d /\ d_small x = d_small d /\ d_cccrc x = d_cccrc d /\ d_sccrc x = d_sccrc d /\
  d_tt x = d_tt d /\ d_ll16 x = d_ll16 d /\ d_ll4 x = d_ll4 d /\ d_cftab x = d_cftab d /\ d_cftabCopy x = d_cftabCopy d /\
  d_verb x = d_verb d /\ d_sv x = d_sv d /\ d_tPos x = d_tPos d /\ d_k0 x = d_k0 d /\ d_nused x = d_nused d /\
  d_out_ch x = d_out_ch d /\ d_out_len x = d_out_len d /\ d_cbcrc x = d_cbcrc d /\ d_rNToGo x = d_rNToGo d /\ d_rTPos x = d_rTPos d /\
  d_tt_al x = d_tt_al d /\ d_ll_al x = d_ll_al d.
(* [comment removed for export] *)
Definition HDR (crc op bno : Z) (x : dst) : Prop := d_origPtr x = op /\ d_rand x = 0 /\ d_sbcrc x = crc /\ d_blockNo x = bno.

Ltac frame_tac H := unfold STATIC, HDR in *; dget; decompose [and] H; repeat split; assumption.

Lemma makeMaps_d_fields : forall x,
  d_inUse (makeMaps_d x) = d_inUse x /\ d_nInUse (makeMaps_d x) = snd (mkmaps 256 0 (d_inUse x) (d_s2u x) 0) /\ d_s2u (makeMaps_d x) = fst (mkmaps 256 0 (d_inUse x) (d_s2u x) 0).
Proof. intros x. unfold makeMaps_d. destruct (mkmaps 256 0 (d_inUse x) (d_s2u x) 0). cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_d_fields : forall f16 bit crc op d, let D := map_d f16 bit crc op d in
  STATIC d D /\ HDR crc op (d_blockNo d + 1) D /\
  d_unzftab D = d_unzftab d /\ d_sel D = d_sel d /\ d_selMtf D = d_selMtf d /\ d_len D = d_len d /\
  d_limit D = d_limit d /\ d_base D = d_base d /\ d_perm D = d_perm d /\ d_minLens D = d_minLens d /\ d_mtfa D = d_mtfa d /\ d_mtfbase D = d_mtfbase d.
Proof.
  intros f16 bit crc op d. cbv zeta. unfold map_d. rewrite makeMaps_d_eq.
  set (G := fun x : dst => STATIC d x /\ HDR crc op (d_blockNo d + 1) x /\
    d_unzftab x = d_unzftab d /\ d_sel x = d_sel d /\ d_selMtf x = d_selMtf d /\ d_len x = d_len d /\
    d_limit x = d_limit d /\ d_base x = d_base d /\ d_perm x = d_perm d /\ d_minLens x = d_minLens d /\ d_mtfa x = d_mtfa d /\ d_mtfbase x = d_mtfbase d).
  enough (GR : G (map_rows 16 0 f16 bit (d_set_inUse (d_set_inUse16 (d_set_state (d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op) 28)
             (zsets 16 0 (fun j : Z => Some (f16 j)) (d_inUse16 (d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op))))
             (clear256 256 0 (d_inUse (d_set_inUse16 (d_set_state (d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op) 28)
             (zsets 16 0 (fun j : Z => Some (f16 j)) (d_inUse16 (d_set_origPtr (d_set_rand (d_set_sbcrc (d_set_blockNo (d_set_state d 27) (d_blockNo d + 1)) crc) 0) op))))))))).
  { set (R := map_rows 16 0 f16 bit _) in *. clearbody R. subst G. cbv beta in GR. frame_tac GR. }
  apply map_rows_frame.
  - intros x v Gx. subst G. cbv beta in *. frame_tac Gx.
  - subst G. cbv beta. unfold STATIC, HDR. dget. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sels_lens_fields : forall msel lnT aS nG nS d, let D := lens_d lnT aS nG (sels_d msel nS nG (d_set_state d 31)) in
  forall d00, (STATIC d00 d -> STATIC d00 D) /\ (forall crc op bno, HDR crc op bno d -> HDR crc op bno D) /\
  d_unzftab D = d_unzftab d /\ d_limit D = d_limit d /\ d_base D = d_base d /\ d_perm D = d_perm d /\ d_minLens D = d_minLens d /\
  d_mtfa D = d_mtfa d /\ d_mtfbase D = d_mtfbase d /\ d_nInUse D = d_nInUse d /\ d_s2u D = d_s2u d /\ d_inUse D = d_inUse d /\
  d_sel D = d_sel (sels_d msel nS nG (d_set_state d 31)).
Proof.
  intros. subst D. unfold lens_d, sels_d. dget. split; [intros H; frame_tac H|]. split; [intros crc op bno H; frame_tac H|].
  repeat split; reflexivity.
Qed.

Lemma make_tables_frame : forall (F : dst -> Prop) n t aS d,
  (forall x li ba pe ml, F x -> F (d_set_minLens (d_set_perm (d_set_base (d_set_limit x li) ba) pe) ml)) -> F d -> F (make_tables n t aS d).
Proof.
  intros F n. induction n as [|n IH]; intros t aS d HF Fd; [exact Fd|].
  rewrite make_tables_S. cbv zeta. destruct (minmax_len _ _ _ _ _ _) as [mn mx]. destruct (hbCreateDecodeTables _ _ _ _ _ _ _ _) as [[li ba] pe].
  apply IH; [exact HF|]. apply HF. exact Fd.
Qed.

(* [comment removed for export] *)
Lemma tables_d_fields : forall L d, let D := tables_d L d in
  forall d00, (STATIC d00 d -> STATIC d00 D) /\ (forall crc op bno, HDR crc op bno d -> HDR crc op bno D) /\
  d_nInUse D = d_nInUse d /\ d_s2u D = d_s2u d /\ d_inUse D = d_inUse d /\ d_sel D = d_sel d /\ d_len D = d_len d /\
  (forall c, 0 <= c < 256 -> zget (d_unzftab D) c = 0) /\
  MINV (d_mtfbase D) /\ (forall k, 0 <= k < 256 -> MV (d_mtfa D) (d_mtfbase D) k = k) /\
  d_limit D = d_limit (make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d) /\
  d_base D = d_base (make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d) /\
  d_perm D = d_perm (make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d) /\
  d_minLens D = d_minLens (make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d).
Proof.
  intros L d. cbv zeta. intros d00. unfold tables_d.
  set (M := make_tables (Z.to_nat (sv_nGroups L)) 0 (sv_alphaSize L) d).
  pose proof (mtf_init_spec (d_set_unzftab M (clear256 256 0 (d_unzftab M)))) as MI. cbv zeta in MI. cps_destruct MI as (MI1 & MI2 & MI3 & MI4).
  set (T := mtf_init (d_set_unzftab M (clear256 256 0 (d_unzftab M)))) in *.
  set (ma := d_mtfa T) in *. set (mb := d_mtfbase T) in *. clearbody ma mb. rewrite MI4. dget.
  assert (FR : forall F : dst -> Prop, (forall x li ba pe ml, F x -> F (d_set_minLens (d_set_perm (d_set_base (d_set_limit x li) ba) pe) ml)) -> F d -> F M).
  { intros F HF Fd. subst M. apply make_tables_frame; [exact HF| exact Fd]. }
  split; [intros H; apply (FR (STATIC d00)); [intros x li ba pe ml Gx; frame_tac Gx| exact H]|].
  split; [intros crc op bno H; apply (FR (HDR crc op bno)); [intros x li ba pe ml Gx; frame_tac Gx| exact H]|].
  split; [apply (FR (fun x => d_nInUse x = d_nInUse d)); [intros; dget; assumption| reflexivity]|].
  split; [apply (FR (fun x => d_s2u x = d_s2u d)); [intros; dget; assumption| reflexivity]|].
  split; [apply (FR (fun x => d_inUse x = d_inUse d)); [intros; dget; assumption| reflexivity]|].
  split; [apply (FR (fun x => d_sel x = d_sel d)); [intros; dget; assumption| reflexivity]|].
  split; [apply (FR (fun x => d_len x = d_len d)); [intros; dget; assumption| reflexivity]|].
  split; [intros c Hc; rewrite clear256_get; replace ((0 <=? c) && (c <? 0 + Z.of_nat 256))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity|].
  split; [exact MI1|]. split; [exact MI2|]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wsum_ext : forall (L L' : Z -> Z) A n, (forall j, 0 <= j < A -> L j = L' j) -> wsum L A n = wsum L' A n.
Proof.
  intros L L' A n H. unfold wsum. apply sumF_ext. intros b Hb. rewrite (H b) by lia. reflexivity.
Qed.

Lemma Lc_In : forall t pi rho, bwt t pi rho -> forall i, (i < length t)%nat -> In (Lc t pi i) t.
Proof.
  intros t pi rho HB i Hi. unfold Lc. apply nth_In. apply prv_lt; [exact (bwt_n t pi rho HB)| apply (bwt_pi_lt t pi rho HB); exact Hi].
Qed.

Lemma ws_sym_legal' : forall (sel : Z -> Z) (Lf : Z -> Z -> Z) A nG nS xs m,
  (forall g, 0 <= g < nS -> 0 <= sel g < nG) ->
  (forall t v, 0 <= t < nG -> 0 <= v < A -> 1 <= Lf t v <= 20) ->
  (forall t k, 0 <= t < nG -> 1 <= k -> wsum (Lf t) A k <= 2 ^ k) ->
  0 <= m -> m + Z.of_nat (length xs) <= 50 * nS -> Forall (fun x => 0 <= x < A) xs ->
  wlegal (ws_sym sel Lf A m xs).
Proof.
  intros sel Lf A nG nS xs. induction xs as [|x xs IH]; intros m HS HL HK Hm HM F; cbn [ws_sym length] in *; [apply wlegal_nil|].
  apply Forall_cons_iff in F as [Fx F].
  assert (HmS : 0 <= m / 50 < nS) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (HS _ HmS) as HT.
  apply wlegal_cons. split; [| apply IH; try assumption; lia].
  pose proof (HL (sel (m / 50)) x HT Fx). split; [lia|].
  apply (ccode_lt (Lf (sel (m / 50))) A); [intros j Hj; pose proof (HL _ j HT Hj); lia| intros k Hk; apply HK; [exact HT| exact Hk]| exact Fx].
Qed.

(* [comment removed for export] *)
Lemma mk_maps_pos : forall n inUse unseq i n0 k, 0 <= i -> i <= k < i + Z.of_nat n -> zget inUse k <> 0 -> 0 <= n0 ->
  n0 + 1 <= snd (mk_maps n inUse unseq i n0).
Proof.
  induction n as [|n IH]; intros inUse unseq i n0 k Hi Hk NZ Hn0; [lia|]. cbn [mk_maps].
  destruct (Z.eqb_spec (zget inUse i) 0) as [E|NE]; cbn [negb].
  - apply (IH _ _ _ _ k); [lia| | exact NZ| lia]. destruct (Z.eq_dec k i); [subst; congruence| lia].
  - pose proof (mkmaps_spec n inUse inUse (zset unseq i n0) (zset unseq i n0) (i + 1) (n0 + 1) ltac:(lia) ltac:(lia) ltac:(intros; reflexivity)) as X.
    destruct (mk_maps n inUse (zset unseq i n0) (i + 1) (n0 + 1)). destruct (mkmaps n (i + 1) inUse (zset unseq i n0) (n0 + 1)). cbn [snd]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DecBlock.
  Variables (t : list Z) (pi rho : nat -> nat).
  Hypothesis HB : bwt t pi rho.
  Let n : nat := length t.

  Variables (crc op : Z) (inUse in160 unseq0 sel selMtf0 pos0 len : zarr) (nG nS : Z) (us : list Z).
  (* [comment removed for export] *)
  Variables (unseq : zarr) (nI : Z).
  Hypothesis Hmaps : mk_maps 256 inUse unseq0 0 0 = (unseq, nI).
  Definition A : Z := nI + 2.
  Definition EOB : Z := nI + 1.
  Definition in16 : zarr := sm_in16 16 in160 inUse 0.
  Definition f16 (i : Z) : Z := bit01 (zget in16 i).
  Definition bit (c : Z) : Z := bit01 (zget inUse c).
  Definition selMtf : zarr := snd (sm_selmtf (Z.to_nat nS) (yy_init (Z.to_nat nG) pos0 0) sel selMtf0 0).
  Definition msel (j : Z) : Z := zget selMtf j.
  Definition lnT (t0 v : Z) : Z := zget len (258 * t0 + v).
  Definition Lf (t0 : Z) : Z -> Z := Lrow len (258 * t0).
  Definition xs : list Z := genc nI EOB (fun k => k) 0 us.
  (* [comment removed for export] *)
  Definition hdr_ws : list (Z * Z) :=
    (ws_blk_hdr crc op ++ ws_bits16 16 f16 0 ++ ws_rows 16 f16 bit 0) ++
    ([(3, nG); (15, nS)] ++ ws_unary (Z.to_nat nS) msel 0 ++ ws_dtables (Z.to_nat nG) lnT (Z.to_nat A) 0 ++ []).
  Definition dec_ws : list (Z * Z) := hdr_ws ++ ws_sym (fun g => zget sel g) Lf A 0 xs.

  Hypothesis Hcrc : 0 <= crc < 4294967296.
  Hypothesis Hop : op = Z.of_nat (origPtr rho).
  Hypothesis IU01 : forall c, 0 <= c < 256 -> zget inUse c = 0 \/ zget inUse c = 1.
  Hypothesis IUt : forall b, In b t -> zget inUse b = 1.
  Hypothesis HnG : 2 <= nG <= 6.
  Hypothesis HnS : 1 <= nS <= 18001.
  Hypothesis Hsel : forall k, 0 <= k < nS -> 0 <= zget sel k < nG.
  Hypothesis Hlen : forall t0 v, 0 <= t0 < nG -> 0 <= v < A -> 1 <= lnT t0 v <= 20.
  Hypothesis Hkraft : forall t0 k, 0 <= t0 < nG -> 1 <= k -> wsum (Lf t0) A k <= 2 ^ k.
  Hypothesis Hus_len : length us = n.
  Hypothesis Hus : forall i, (i < n)%nat -> nth i us 0 = zget unseq (Lc t pi i).
  Hypothesis Hxs : Z.of_nat (length xs) <= 50 * nS.
  Hypothesis Hn20 : Z.of_nat n < 2 ^ 20.

  Let Hn1 : (0 < n)%nat := bwt_n t pi rho HB.

  (* [comment removed for export] *)
  Definition Dm (d : dst) : dst := map_d f16 bit crc op d.
  Definition L1 (L : dsv) : dsv := sv_set_alphaSize (sv_set_i (if anyrow 16 0 f16 then sv_set_j L 16 else L) 16) (nI + 2).
  Definition D4 (d : dst) : dst := lens_d lnT A nG (sels_d msel nS nG (d_set_state (Dm d) 31)).
  Definition L4 (L : dsv) : dsv := lens_L msel lnT A nG nS (L1 L).
  Definition D0 (L : dsv) (d : dst) : dst := tables_d (L4 L) (D4 d).
  Definition L0 (L : dsv) (d : dst) : dsv := tables_L (L4 L) (D4 d).
  (* [comment removed for export] *)
  Local Strategy expand [Dm L1 D4 L4 D0 L0].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma nI_range : 1 <= nI <= 256.
  Proof.
    pose proof (nth_In t 0 Hn1) as IN. pose proof (IUt _ IN) as U.
    pose proof (bwt_bytes t pi rho HB) as BY. rewrite Forall_forall in BY. specialize (BY _ IN).
    pose proof (mkmaps_spec 256 inUse inUse unseq0 unseq0 0 0 ltac:(lia) ltac:(lia) ltac:(intros; reflexivity)) as X.
    pose proof (mk_maps_pos 256 inUse unseq0 0 0 (nth 0 t 0) ltac:(lia) ltac:(change (Z.of_nat 256) with 256; lia) ltac:(rewrite U; lia) ltac:(lia)) as P.
    rewrite Hmaps in X, P. destruct (mkmaps 256 0 inUse unseq0 0). cbn [snd] in *. change (Z.of_nat 256) with 256 in X. lia.
  Qed.

  Lemma Dm_maps : forall d, let D := Dm d in
    d_nInUse D = nI /\
    (forall k, 0 <= k < 256 -> zget inUse k <> 0 -> 0 <= zget unseq k < nI /\ zget (d_s2u D) (zget unseq k) = k) /\
    (forall v, 0 <= v < nI -> 0 <= zget (d_s2u D) v < 256).
  Proof.
    intros d. cbv zeta. unfold Dm.
    assert (ZP : forall k, 0 <= k < 0 + Z.of_nat 256 -> (zget inUse k =? 0) = (zget (d_inUse (map_d f16 bit crc op d)) k =? 0)).
    { intros k Hk. pose proof (map_d_inUse inUse in160 crc op d k ltac:(change (Z.of_nat 256) with 256 in Hk; lia)) as M. cbv zeta in M.
      symmetry. exact M. }
    revert ZP. unfold map_d.
    match goal with |- context [makeMaps_d ?r] => set (R := r) end.
    cps_destruct (makeMaps_d_fields R) as (F1 & F2 & F3). rewrite F1, F2, F3. clearbody R. intros ZP.
    pose proof (mkmaps_spec 256 inUse (d_inUse R) unseq0 (d_s2u R) 0 0 ltac:(lia) ltac:(lia) ZP) as X.
    rewrite Hmaps in X. destruct (mkmaps 256 0 (d_inUse R) (d_s2u R) 0) as [s2 nD]. cbn [fst snd] in *.
    cps_destruct X as (E1 & E2 & E3 & E4 & E5 & E6). change (Z.of_nat 256) with 256 in *.
    split; [symmetry; exact E1|]. split.
    - intros k Hk NZ. destruct (E3 k ltac:(lia) NZ) as [B1 B2]. split; [lia| exact B2].
    - intros v Hv. cps_destruct (E4 v ltac:(lia)) as (B1 & _ & _). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma f16_01 : forall j, f16 j = 0 \/ f16 j = 1. Proof. intros j. unfold f16. apply bit01_range. Qed.
  Lemma bit_01 : forall c, bit c = 0 \/ bit c = 1. Proof. intros c. unfold bit. apply bit01_range. Qed.
  Lemma msel_range : forall k, 0 <= k < nS -> 0 <= msel k < nG.
  Proof. intros k Hk. unfold msel, selMtf. apply (sels_d_spec nG nS sel selMtf0 pos0 dst_zero k); try lia. exact Hsel. Qed.
  Lemma origPtr_ltn : (origPtr rho < n)%nat.
  Proof. apply (origPtr_lt t Hn1 rho). apply (bwt_rho_lt t pi rho HB). Qed.
  Lemma ws_dtables_legal' : forall k lnT0 aS t0, (forall t', t0 <= t' < t0 + Z.of_nat k -> 0 <= lnT0 t' 0 < 32) -> wlegal (ws_dtables k lnT0 aS t0).
  Proof.
    induction k as [|k IH]; intros lnT0 aS t0 H; cbn [ws_dtables]; [apply wlegal_nil|].
    apply wlegal_app. split; [| apply IH; intros; apply H; lia].
    apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 5) with 32; pose proof (H t0 ltac:(lia)); lia| apply ws_drow_legal].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma hdr_ws_legal : wlegal hdr_ws.
  Proof.
    unfold hdr_ws. pose proof origPtr_ltn as OP. rewrite app_nil_r. pose proof nI_range as NI.
    apply wlegal_app; split.
    { apply wlegal_app; split; [apply ws_blk_hdr_legal; lia|]. apply wlegal_app; split; [apply ws_bits16_legal; apply f16_01| apply ws_rows_legal; apply bit_01]. }
    apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 3) with 8; lia|]. apply wlegal_cons. split; [cbn [fst snd]; change (2 ^ 15) with 32768; lia|].
    apply wlegal_app; split; [apply ws_unary_legal|].
    apply ws_dtables_legal'. intros t' Ht'. pose proof (Hlen t' 0 ltac:(lia) ltac:(unfold A; lia)). lia.
  Qed.

  Lemma feed36 : forall L d s, Z.of_nat n <= 100000 * d_bs100k d ->
    dfeed hdr_ws (DGo 14 L d s) = Some (DGo 36 (L0 L d) (D0 L d) s).
  Proof.
    intros L d s Hcap. pose proof origPtr_ltn as OP. pose proof nI_range as NI. cps_destruct (Dm_maps d) as (N1 & _ & _).
    unfold hdr_ws. rewrite dfeed_app.
    rewrite (seg_hdr_map crc op f16 bit L d s Hcrc ltac:(lia) ltac:(lia) ltac:(intros; apply f16_01)). cbv zeta.
    unfold Dm in N1. rewrite N1. replace (nI =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (seg_sels_tabs nG nS A msel lnT); try lia.
    - rewrite dfeed_nil. reflexivity.
    - dget. unfold A. reflexivity.
    - unfold BZ_MAX_SELECTORS. lia.
    - unfold A. lia.
    - apply msel_range.
    - exact Hlen.
  Qed.

  Lemma L4_fields : forall L, sv_alphaSize (L4 L) = A /\ sv_nGroups (L4 L) = nG /\ sv_nSelectors (L4 L) = nS.
  Proof. intros L. unfold L4, L1, lens_L. dget. unfold A. repeat split; reflexivity. Qed.

  Lemma at36L : forall L d,
    sv_alphaSize (L0 L d) = A /\ sv_nSelectors (L0 L d) = nS /\ sv_nGroups (L0 L d) = nG /\ sv_nblockMAX (L0 L d) = 100000 * d_bs100k (D0 L d) /\
    sv_groupNo (L0 L d) = 0 /\ sv_groupPos (L0 L d) = BZ_G_SIZE - 1 /\ sv_gSel (L0 L d) = zget (d_sel (D0 L d)) 0 /\
    sv_gMinlen (L0 L d) = zget (d_minLens (D0 L d)) (zget (d_sel (D0 L d)) 0) /\
    sv_zn (L0 L d) = zget (d_minLens (D0 L d)) (zget (d_sel (D0 L d)) 0) /\ sv_nblock (L0 L d) = 0 /\ sv_gPtr (L0 L d) = true /\ sv_EOB (L0 L d) = d_nInUse (D0 L d) + 1.
  Proof.
    intros L d. unfold L0, tables_L. set (TD := tables_d (L4 L) (D4 d)). unfold L4, L1, lens_L. dget. subst TD. unfold A.
    repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma at36 : forall L d, Z.of_nat n <= 100000 * d_bs100k d ->
    STATIC d (D0 L d) /\ HDR crc op (d_blockNo d + 1) (D0 L d) /\
    d_nInUse (D0 L d) = nI /\
    (forall k, 0 <= k < 256 -> zget inUse k <> 0 -> 0 <= zget unseq k < nI /\ zget (d_s2u (D0 L d)) (zget unseq k) = k) /\
    (forall v, 0 <= v < nI -> 0 <= zget (d_s2u (D0 L d)) v < 256) /\
    (forall k, 0 <= k < nS -> zget (d_sel (D0 L d)) k = zget sel k) /\
    (forall t0 v, 0 <= t0 < nG -> 0 <= v < A -> Lrow (d_len (D0 L d)) (258 * t0) v = lnT t0 v) /\
    (forall t0, 0 <= t0 < nG -> exists mn mx, grp_ok A (d_len (D0 L d)) (d_limit (D0 L d)) (d_base (D0 L d)) (d_perm (D0 L d)) (d_minLens (D0 L d)) t0 mn mx) /\
    (forall c, 0 <= c < 256 -> zget (d_unzftab (D0 L d)) c = 0) /\
    MINV (d_mtfbase (D0 L d)) /\ (forall k, 0 <= k < 256 -> MV (d_mtfa (D0 L d)) (d_mtfbase (D0 L d)) k = k) /\
    sv_alphaSize (L0 L d) = A /\ sv_EOB (L0 L d) = nI + 1 /\ sv_nSelectors (L0 L d) = nS /\ sv_nGroups (L0 L d) = nG /\ sv_nblockMAX (L0 L d) = 100000 * d_bs100k d /\
    sv_groupNo (L0 L d) = 0 /\ sv_groupPos (L0 L d) = BZ_G_SIZE - 1 /\ sv_gSel (L0 L d) = zget (d_sel (D0 L d)) 0 /\ sv_gMinlen (L0 L d) = zget (d_minLens (D0 L d)) (zget (d_sel (D0 L d)) 0) /\
    sv_zn (L0 L d) = zget (d_minLens (D0 L d)) (zget (d_sel (D0 L d)) 0) /\ sv_nblock (L0 L d) = 0 /\ sv_gPtr (L0 L d) = true.
  Proof.
    intros L d Hcap. pose proof nI_range as NI.
    cps_destruct (Dm_maps d) as (N1 & N2 & N3).
    assert (MF : let D := Dm d in STATIC d D /\ HDR crc op (d_blockNo d + 1) D /\
      d_unzftab D = d_unzftab d /\ d_sel D = d_sel d /\ d_selMtf D = d_selMtf d /\ d_len D = d_len d /\
      d_limit D = d_limit d /\ d_base D = d_base d /\ d_perm D = d_perm d /\ d_minLens D = d_minLens d /\ d_mtfa D = d_mtfa d /\ d_mtfbase D = d_mtfbase d)
      by exact (map_d_fields f16 bit crc op d).
    cbv zeta in MF. cps_destruct MF as (MS & MH & Munz & Msel & MselMtf & Mlen & Mlim & Mbase & Mperm & Mmin & Mma & Mmb).
    assert (SF : let D := D4 d in forall d00, (STATIC d00 (Dm d) -> STATIC d00 D) /\ (forall crc op bno, HDR crc op bno (Dm d) -> HDR crc op bno D) /\
      d_unzftab D = d_unzftab (Dm d) /\ d_limit D = d_limit (Dm d) /\ d_base D = d_base (Dm d) /\ d_perm D = d_perm (Dm d) /\ d_minLens D = d_minLens (Dm d) /\
      d_mtfa D = d_mtfa (Dm d) /\ d_mtfbase D = d_mtfbase (Dm d) /\ d_nInUse D = d_nInUse (Dm d) /\ d_s2u D = d_s2u (Dm d) /\ d_inUse D = d_inUse (Dm d) /\
      d_sel D = d_sel (sels_d msel nS nG (d_set_state (Dm d) 31)))
      by exact (sels_lens_fields msel lnT A nG nS (Dm d)).
    cbv zeta in SF. cps_destruct (SF d) as (SS & SH & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11). clear SF.
    assert (TF : let D := D0 L d in forall d00, (STATIC d00 (D4 d) -> STATIC d00 D) /\ (forall crc op bno, HDR crc op bno (D4 d) -> HDR crc op bno D) /\
      d_nInUse D = d_nInUse (D4 d) /\ d_s2u D = d_s2u (D4 d) /\ d_inUse D = d_inUse (D4 d) /\ d_sel D = d_sel (D4 d) /\ d_len D = d_len (D4 d) /\
      (forall c, 0 <= c < 256 -> zget (d_unzftab D) c = 0) /\
      MINV (d_mtfbase D) /\ (forall k, 0 <= k < 256 -> MV (d_mtfa D) (d_mtfbase D) k = k) /\
      d_limit D = d_limit (make_tables (Z.to_nat (sv_nGroups (L4 L))) 0 (sv_alphaSize (L4 L)) (D4 d)) /\
      d_base D = d_base (make_tables (Z.to_nat (sv_nGroups (L4 L))) 0 (sv_alphaSize (L4 L)) (D4 d)) /\
      d_perm D = d_perm (make_tables (Z.to_nat (sv_nGroups (L4 L))) 0 (sv_alphaSize (L4 L)) (D4 d)) /\
      d_minLens D = d_minLens (make_tables (Z.to_nat (sv_nGroups (L4 L))) 0 (sv_alphaSize (L4 L)) (D4 d)))
      by exact (tables_d_fields (L4 L) (D4 d)).
    cbv zeta in TF. cps_destruct (TF d) as (TS & TH & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12). clear TF.
    cps_destruct (L4_fields L) as (AL & GL & SL).
    rewrite AL, GL in T9, T10, T11, T12.
    assert (LD : (forall t0 v, 0 <= t0 < nG -> 0 <= v < A -> zget (d_len (D4 d)) (258 * t0 + v) = lnT t0 v) /\
                 (forall c, (c < 0 \/ 258 * nG <= c \/ A <= c mod 258) -> zget (d_len (D4 d)) c = zget (d_len (sels_d msel nS nG (d_set_state (Dm d) 31))) c))
      by exact (lens_d_spec lnT A nG (sels_d msel nS nG (d_set_state (Dm d) 31)) ltac:(unfold A; lia) ltac:(lia)).
    destruct LD as [LD1 LD2].
    assert (ROWS : forall t0 v, 0 <= t0 < nG -> 0 <= v < A -> Lrow (d_len (D4 d)) (258 * t0) v = lnT t0 v) by (intros; unfold Lrow; apply LD1; lia).
    assert (ROWS' : forall t0 v, 0 <= t0 < 0 + Z.of_nat (Z.to_nat nG) -> 0 <= v < A -> 1 <= Lrow (d_len (D4 d)) (258 * t0) v <= 20).
    { intros t0 v Ht0 Hv. rewrite ROWS by lia. apply Hlen; lia. }
    pose proof (make_tables_spec A (d_len (D4 d)) ltac:(unfold A; lia) (Z.to_nat nG) 0 (D4 d) ltac:(lia) eq_refl ROWS') as MT. cbv zeta in MT. destruct MT as (MT1 & _).
    split; [apply TS; apply SS; exact MS|]. split; [apply TH; apply SH; exact MH|].
    split; [rewrite T1, S8; exact N1|]. split; [rewrite T2, S9; exact N2|]. split; [rewrite T2, S9; exact N3|].
    split; [intros k Hk; rewrite T4, S11; apply (sels_d_spec nG nS sel selMtf0 pos0 _ k); try lia; exact Hsel|].
    split; [rewrite T5; exact ROWS|].
    split; [intros t0 Ht0; rewrite T5, T9, T10, T11, T12; apply MT1; lia|].
    split; [exact T6|]. split; [exact T7|]. split; [exact T8|].
    cps_destruct (at36L L d) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    rewrite G12, T1, S8, N1. rewrite G4. destruct (TS (SS MS)) as (B1 & _). rewrite B1.
    split; [exact G1|]. split; [reflexivity|]. split; [exact G2|]. split; [exact G3|]. split; [reflexivity|]. split; [exact G5|].
    split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|]. split; [exact G10| exact G11].
  Qed.

  Lemma hyps36 : forall L d B V, Z.of_nat n <= 100000 * d_bs100k d -> sym_hyps (L0 L d) (setLB (D0 L d) B V).
  Proof.
    intros L d B V Hcap. pose proof nI_range as NI.
    cps_destruct (at36 L d Hcap) as (TS & TH & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    unfold sym_hyps. autorewrite with lb. cbv zeta. rewrite F1, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12.
    split; [exact NI|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [intros g Hg; rewrite F4 by lia; apply Hsel; lia|].
    split; [exact F6|].
    split; [intros t0 k Ht0 Hk; rewrite (wsum_ext (Lrow (d_len (D0 L d)) (258 * t0)) (Lf t0) A k) by (intros j Hj; rewrite F5 by lia; reflexivity); apply Hkraft; lia|].
    split; [split; [exact F8| exact F9]|]. split; [exact F7|]. split; [exact F3|].
    repeat split; try reflexivity. destruct TS as (B1 & _). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ccode_ext : forall (Lx Ly : Z -> Z) Ax i, (forall j, 0 <= j < Ax -> Lx j = Ly j) -> 0 <= i < Ax -> ccode Lx Ax i = ccode Ly Ax i.
  Proof.
    intros Lx Ly Ax i H Hi. unfold ccode. apply sumF_ext. intros b Hb. unfold lexb. rewrite !H by lia. reflexivity.
  Qed.
  Lemma ws_sym_ext : forall (selx sely : Z -> Z) (Lfx Lfy : Z -> Z -> Z) Ax nGx ys m, 0 <= m ->
    (forall k, m <= k < m + Z.of_nat (length ys) -> selx (k / 50) = sely (k / 50) /\ 0 <= selx (k / 50) < nGx) ->
    (forall t0 v, 0 <= t0 < nGx -> 0 <= v < Ax -> Lfx t0 v = Lfy t0 v) ->
    Forall (fun x => 0 <= x < Ax) ys ->
    ws_sym selx Lfx Ax m ys = ws_sym sely Lfy Ax m ys.
  Proof.
    intros selx sely Lfx Lfy Ax nGx ys. induction ys as [|y ys IH]; intros m Hm HS HL F; cbn [ws_sym length] in *; [reflexivity|].
    apply Forall_cons_iff in F as [Fy F]. destruct (HS m ltac:(lia)) as [E R]. rewrite <- E.
    rewrite (HL _ y R Fy). rewrite (ccode_ext (Lfx (selx (m / 50))) (Lfy (selx (m / 50))) Ax y) by (try exact Fy; intros j Hj; apply HL; lia).
    f_equal. apply IH; [lia| intros k Hk; apply HS; lia| exact HL| exact F].
  Qed.

  Lemma us_range : Forall (fun u => 0 <= u < nI) us.
  Proof.
    cps_destruct (Dm_maps dst_zero) as (_ & N2 & _).
    apply Forall_nth. intros i dflt Hi. rewrite (nth_indep _ dflt 0) by exact Hi. rewrite Hus by lia.
    pose proof (Lc_In t pi rho HB i ltac:(lia)) as IN. pose proof (IUt _ IN) as U.
    pose proof (bwt_bytes t pi rho HB) as BY. rewrite Forall_forall in BY. specialize (BY _ IN).
    apply (proj1 (N2 (Lc t pi i) BY ltac:(rewrite U; lia))).
  Qed.
  Lemma xs_facts : (exists body, xs = body ++ [EOB] /\ Forall (fun x => 0 <= x < EOB) body) /\ runs_ok 20 0 xs /\
    a_out (asteps EOB ast0 xs) = us /\ Forall (fun x => 0 <= x < A) xs.
  Proof.
    pose proof nI_range as NI. pose proof us_range as UR. unfold xs, EOB, A.
    cps_destruct (genc_shape nI (nI + 1) ltac:(lia) eq_refl us (fun k => k) 0 (MPERM_id nI) UR ltac:(lia)) as (body & E & FB).
    split; [exists body; auto|].
    split; [exact (genc_runs_ok nI (nI + 1) ltac:(lia) eq_refl us (fun k => k) 0 (MPERM_id nI) UR ltac:(lia) ltac:(rewrite Hus_len; lia))|].
    split.
    - unfold ast0. rewrite (genc_inverse nI (nI + 1) us (fun k => k) [] 0 ltac:(lia) eq_refl (MPERM_id nI) UR ltac:(lia)
                             ltac:(rewrite Hus_len; change (2 ^ 64) with 18446744073709551616; lia)). reflexivity.
    - rewrite E. apply Forall_app. split; [eapply Forall_impl; [| exact FB]; cbv beta; intros; lia| constructor; [lia| constructor]].
  Qed.

  Lemma rd_bend : forall sm0 d' cf cc tt l16 l4 s0, let dX := bend_upd t pi rho sm0 d' cf cc tt l16 l4 in
    rd_abs dX s0 = rd_abs d' s0 /\ (rd_ok d' s0 -> rd_ok dX s0) /\ (forall d1 s1, dcost d1 s1 dX s0 = dcost d1 s1 d' s0).
  Proof.
    intros. pose proof (bend_upd_fields t pi rho sm0 d' cf cc tt l16 l4) as X. cbv zeta in X. decompose [and] X.
    subst dX. split; [unfold rd_abs; rewrite H19, H20; reflexivity|].
    split; [unfold rd_ok; rewrite H19, H20; tauto|].
    intros d1 s1. unfold dcost, rd_abs. rewrite H19, H20. reflexivity.
  Qed.

  Lemma smallb_ext : forall x y, d_small x = d_small y -> smallb x = smallb y.
  Proof. intros x y E. unfold smallb. rewrite E. reflexivity. Qed.
  Lemma hist_Lcnt : forall (s2u : Z -> Z) c, (forall j, (j < n)%nat -> s2u (nth j us 0) = Lc t pi j) -> hist s2u us c = Lcnt t pi c.
  Proof. intros s2u c H. unfold hist, Lcnt. rewrite Hus_len. apply cnt_ext. intros j Hj. rewrite (H j Hj). reflexivity. Qed.
  Lemma s2u_unseq : forall L d, Z.of_nat n <= 100000 * d_bs100k d -> forall i, (i < n)%nat -> zget (d_s2u (D0 L d)) (zget unseq (Lc t pi i)) = Lc t pi i.
  Proof.
    intros L d Hcap i Hi. cps_destruct (at36 L d Hcap) as (_ & _ & _ & F2 & _).
    assert (IN : In (Lc t pi i) t) by (apply (Lc_In t pi rho HB); exact Hi).
    assert (BYi : 0 <= Lc t pi i < 256) by (pose proof (bwt_bytes t pi rho HB) as BY; rewrite Forall_forall in BY; apply BY; exact IN).
    destruct (F2 (Lc t pi i) BYi ltac:(rewrite (IUt _ IN); lia)) as [_ E2]. exact E2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma to_final : forall L d s rest,
    rd_ok d s -> bits_ok rest -> rd_abs d s = bapp (wbits dec_ws) rest -> Z.of_nat n <= 100000 * d_bs100k d ->
    exists k L' d' s2 kb B V,
      (forall f, drun (k + f) 14 L d s = dgo f (block_end L' d' s2)) /\
      FINAL (L0 L d) (setLB (D0 L d) B V) (asteps (nI + 1) ast0 xs) L' d' /\
      rd_abs d' s2 = rest /\ rd_ok d' s2 /\ Z.of_nat k <= dcost d s d' s2 /\ consumed_from kb s s2.
  Proof.
    intros L d s rest RD BO AB Hcap. pose proof nI_range as NI.
    cps_destruct xs_facts as ((body & XE & FB) & RO & AOUT & FX).
    cps_destruct (at36 L d Hcap) as (TS & TH & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    pose proof hdr_ws_legal as WL1.
    assert (WL2 : wlegal (ws_sym (fun g => zget sel g) Lf A 0 xs)).
    { apply (ws_sym_legal' _ _ A nG nS xs 0 Hsel); [intros; unfold Lf, Lrow; apply Hlen; lia| exact Hkraft| lia| cbn [Z.add]; lia| exact FX]. }
    unfold dec_ws in AB. rewrite wbits_app in AB by assumption.
    rewrite bapp_assoc in AB by (first [apply wbits_len; exact WL2| exact (proj1 BO)]).
    set (rest' := bapp (wbits (ws_sym (fun g => zget sel g) Lf A 0 xs)) rest) in AB.
    assert (BO' : bits_ok rest') by (apply bapp_ok; [apply wbits_ok; exact WL2| exact BO]).
    cps_destruct (drun_feed hdr_ws 14 L d s rest' _ WL1 RD BO' AB (feed36 L d s Hcap)) as (k1 & B & V & s1 & kb1 & RUN1 & REST1 & CF1).
    cps_destruct (REST1 (D0 L d)) as (AB1 & RO1 & CO1).
    assert (SYM : ws_sym (fun g => zget sel g) Lf A 0 xs =
                  ws_sym (fun g => zget (d_sel (setLB (D0 L d) B V)) g) (fun t0 => Lrow (d_len (setLB (D0 L d) B V)) (258 * t0)) (sv_alphaSize (L0 L d)) 0 xs).
    { abstract (rewrite G1; autorewrite with lb; apply (ws_sym_ext _ _ _ _ A nG); [lia| | | exact FX];
      [ intros k Hk; assert (HK : 0 <= k / 50 < nS) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]); rewrite F4 by exact HK; split; [reflexivity| apply Hsel; exact HK]
      | intros t0 v Ht0 Hv; unfold Lf; symmetry; apply F5; lia]). }
    unfold EOB in XE, FB, RO, AOUT.
    assert (XE' : xs = body ++ [sv_EOB (L0 L d)]) by (rewrite G2; exact XE).
    assert (FB' : Forall (fun x => 0 <= x < sv_EOB (L0 L d)) body) by (rewrite G2; exact FB).
    assert (HL1 : Z.of_nat (length xs) <= BZ_G_SIZE * sv_nSelectors (L0 L d)) by (rewrite G3; unfold BZ_G_SIZE; lia).
    assert (HL2 : Z.of_nat (length (a_out (asteps (sv_EOB (L0 L d)) ast0 xs))) <= sv_nblockMAX (L0 L d)) by (rewrite G2, G5, AOUT, Hus_len; lia).
    assert (AB1' : rd_abs (setLB (D0 L d) B V) s1 =
                   bapp (wbits (ws_sym (fun g => zget (d_sel (setLB (D0 L d) B V)) g) (fun t0 => Lrow (d_len (setLB (D0 L d) B V)) (258 * t0)) (sv_alphaSize (L0 L d)) 0 xs)) rest)
      by (rewrite <- SYM; exact AB1).
    cps_destruct (sym_phase (L0 L d) (setLB (D0 L d) B V) xs body s1 rest (hyps36 L d B V Hcap) XE' FB' RO HL1 HL2 RO1 BO AB1')
      as (k2 & L' & d' & s2 & kb2 & RUN2 & FIN & AB2 & RO2 & CO2 & CF2).
    rewrite G2 in FIN.
    exists (k1 + k2)%nat, L', d', s2, (kb1 + kb2)%nat, B, V.
    split. { abstract (intros f; replace (k1 + k2 + f)%nat with (k1 + (k2 + f))%nat by lia; rewrite RUN1; cbn [dres_map2 dgo]; unfold FLB; apply RUN2). }
    split; [exact FIN|]. split; [exact AB2|]. split; [exact RO2|].
    split. { abstract (rewrite (dcost_trans d s (setLB (D0 L d) B V) s1 d' s2); lia). }
    eapply consumed_from_trans; [exact CF1| exact CF2].
  Time Qed.

  Theorem dec_block : forall L d s rest,
    rd_ok d s -> bits_ok rest -> rd_abs d s = bapp (wbits dec_ws) rest -> Z.of_nat n <= 100000 * d_bs100k d ->
    exists k L' d' s1 kb cf cc tt l16 l4,
      let sm := smallb d in let dX := bend_upd t pi rho sm d' cf cc tt l16 l4 in
      (forall f, drun (k + f) 14 L d s = dgo f (DRet BZ_OK (bend_L t pi rho sm L') dX s1)) /\
      Z.of_nat k <= dcost d s dX s1 /\ consumed_from kb s s1 /\
      rd_abs dX s1 = rest /\ rd_ok dX s1 /\ TV t pi rho sm dX /\ sv_nblock L' = Z.of_nat n /\
      d_sbcrc d' = crc /\ d_cccrc d' = d_cccrc d /\ d_bs100k d' = d_bs100k d /\ d_small d' = d_small d /\ d_blockNo d' = d_blockNo d + 1.
  Proof.
    intros L d s rest RD BO AB Hcap. pose proof nI_range as NI.
    cps_destruct (to_final L d s rest RD BO AB Hcap) as (k & L' & d' & s2 & kb & B & V & RUN & FIN & AB2 & RO2 & CO & CF).
    cps_destruct (at36 L d Hcap) as (TS & TH & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
    cps_destruct xs_facts as (_ & _ & AOUT & _). unfold EOB in AOUT.
    cps_destruct FIN as (ns & es & N & zvec & zj & gNo & gPos & gSel & gMinlen & zn & tt & l16 & unz & ma & mb & lbl & B' & V' & HL' & Hns & HD' & Fout & PRE & FRM & HI1 & HI2).
    rewrite AOUT in HL', PRE, HI1, Fout.
    pose proof (symd_upd_fields (setLB (D0 L d) B V) tt l16 unz ma mb lbl B' V') as DF. cbv zeta in DF. rewrite <- HD' in DF.
    cps_destruct DF as (Dtt & Dl16 & Dunz & _ & _ & _ & _ & _ & _ & _ & Drand & _ & _ & Dbs & Dsm & Dbno & _ & Dop & _ & _ & _ & _ & _ & _ & _ & _ & Dsb & Dsc & Dcb & Dcc & _).
    autorewrite with lb in Dtt, Dl16, Dunz, Drand, Dbs, Dsm, Dbno, Dop, Dsb, Dsc, Dcb, Dcc.
    cps_destruct TS as (Sbs & Ssm & Scc & _). cps_destruct TH as (Hop' & Hrand & Hsb & Hbno).
    assert (SMd : smallb d' = smallb d) by (unfold smallb; rewrite Dsm, Ssm; reflexivity).
    cps_destruct (block_end_ok t pi rho HB (smallb d) L' d' s2) as (cf & cc & tt' & l16' & l4 & BE & TVx).
    - abstract (rewrite HL'; cbn; rewrite Hus_len; reflexivity).
    - exact SMd.
    - rewrite Drand. exact Hrand.
    - (* [comment removed for export] *)
      abstract (intros i Hi; specialize (PRE i ltac:(rewrite Hus_len; exact Hi)); rewrite Hus in PRE by exact Hi;
        rewrite lb_smallb, lbg_s2u, (s2u_unseq L d Hcap i Hi), (smallb_ext _ _ Ssm), <- Dtt, <- Dl16 in PRE; exact PRE).
    - abstract (unfold HIST; intros c Hc; rewrite Dunz, HI1 by lia; rewrite lbg_s2u; apply (f_equal Z.of_nat); apply hist_Lcnt;
        intros j Hj; rewrite Hus by exact Hj; apply (s2u_unseq L d Hcap j Hj)).
    - rewrite Dop, Hop'. exact Hop.
    - rewrite Dbs, Sbs. exact Hcap.
    - intros _. exact Hn20.
    - cps_destruct (rd_bend (smallb d) d' cf cc tt' l16' l4 s2) as (RA & RK & RC).
      exists k, L', d', s2, kb, cf, cc, tt', l16', l4. cbv zeta.
      split. { abstract (intros f; rewrite RUN, BE; reflexivity). }
      split. { rewrite RC. exact CO. }
      split. { exact CF. }
      split. { rewrite RA. exact AB2. }
      split. { apply RK. exact RO2. }
      split. { exact TVx. }
      split. { abstract (rewrite HL'; cbn; rewrite Hus_len; reflexivity). }
      split. { rewrite Dsb. exact Hsb. }
      split. { rewrite Dcc. exact Scc. }
      split. { rewrite Dbs. exact Sbs. }
      split. { rewrite Dsm. exact Ssm. }
      rewrite Dbno. exact Hbno.
  Time Qed.
End DecBlock.

(* [comment removed for export] *)

