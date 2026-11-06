(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK A0F_decK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK BzDU7 DecAuxM DecTacM DecCutFA A0F_decV S0F_dec_U4A S0F_dec_U7D S0F_dec_U7B.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Section DECX.
Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition dfp (cx : bctx) (x : Z) : Prop :=
  (b_s cx <= x < b_s cx + 64144) \/ (b_strm cx <= x < b_strm cx + 80) \/ (b_src cx <= x < b_src cx + b_len cx) \/ ~ outside (blk_ivls cx) x.

Ltac ag_sub AG := eapply agree_sub; [exact AG|]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in Hx.

Lemma drest_agree : forall (m m' : mem) S r (P : Z -> Prop), drest_at a0segs m S r ->
  agree_on P m m' -> (forall x, S + 68 <= x < S + 64036 -> P x) -> drest_at a0segs m' S r.
Proof.
  intros m m' S r P D AG SUB.
  destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
  unfold drest_at.
  repeat match goal with
  | |- _ /\ _ => split
  | |- Z.of_nat _ = _ => assumption
  | H : u32arr _ m ?a ?ws |- u32arr _ m' ?a ?ws => apply (n_u32arr_agree a0segs m m' a ws H); ag_sub AG; apply SUB; lia
  | H : u8arr _ m ?a ?bs |- u8arr _ m' ?a ?bs => apply (n_u8arr_agree a0segs m m' a bs H); ag_sub AG; apply SUB; lia
  end.
Qed.

Lemma blk_agree : forall (m m' : mem) cx k (P : Z -> Prop), blk_at a0segs m cx k ->
  agree_on P m m' -> (forall x, ~ outside (blk_ivls cx) x -> P x) -> blk_at a0segs m' cx k.
Proof.
  intros m m' cx k P B AG SUB. destruct k as [ttw|l16 l4]; cbn [blk_at] in *.
  - destruct B as (S0 & U & L). split; [exact S0|]. split; [| exact L].
    apply (n_u32arr_agree a0segs m m' _ _ U). ag_sub AG. apply SUB. unfold blk_ivls. rewrite S0. cbn [Z.eqb outside]. lia.
  - destruct B as (S1 & U1 & L1 & U2 & L2). split; [exact S1|]. split; [| split; [exact L1| split; [| exact L2]]].
    + apply (n_u8arr_agree a0segs m m' _ _ U1). ag_sub AG. apply SUB. unfold blk_ivls. rewrite S1. cbn [Z.eqb outside]. lia.
    + apply (n_u8arr_agree a0segs m m' _ _ U2). ag_sub AG. apply SUB. unfold blk_ivls. rewrite S1. cbn [Z.eqb outside]. lia.
Qed.

(* [comment removed for export] *)
Lemma dmemL_agree : forall cx payload (m m' : mem) v, Z.of_nat (length payload) = b_len cx -> Z.of_nat (length (dv_cf v)) = 257 ->
  agree_on (dfp cx) m m' -> dmemL cx payload m v -> dmemL cx payload m' v.
Proof.
  intros cx payload m m' v PL CFL AG (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold dmemL.
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H1). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. unfold dfp. lia. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H2). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. unfold dfp. lia. }
  split. { apply (n_u32arr_agree a0segs m m' _ _ H3). ag_sub AG. unfold dfp. lia. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H4). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. unfold dfp. lia. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H5). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. unfold dfp. lia. }
  split. { apply (drest_agree m m' _ _ _ H6 AG). intros x Hx. unfold dfp. lia. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H7). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. unfold dfp. lia. }
  split. { apply (blk_agree m m' _ _ _ H8 AG). intros x Hx. unfold dfp. tauto. }
  apply (bytes_at_agree a0segs m m' _ _ H9). ag_sub AG. unfold dfp. lia.
Qed.

Lemma dmemLF_agree : forall cx payload (m m' : mem) J d s, Z.of_nat (length payload) = b_len cx ->
  agree_on (dfp cx) m m' -> dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m' (dvF cx J d s).
Proof. intros cx payload m m' J d s PL AG H. apply (dmemL_agree cx payload m m' _ PL); [cbn [dvF dv_cf]; apply zw32_length; lia| exact AG| exact H]. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dmemL_rest : forall cx payload (m m' : mem) J d d' s (Hole : Z -> Prop), Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ ~ Hole x) m m' ->
  (forall x, Hole x -> (b_s cx + 68 <= x < b_s cx + 1092) \/ (b_s cx + 2124 <= x < b_s cx + 3152) \/ (b_s cx + 3196 <= x < b_s cx + 64036)) ->
  (forall x, Hole x -> ~ (b_strm cx <= x < b_strm cx + 80) /\ ~ (b_src cx <= x < b_src cx + b_len cx) /\ outside (blk_ivls cx) x) ->
  hd_of cx J d' = hd_of cx J d -> d_nused d' = d_nused d -> d_cftab d' = d_cftab d -> mid_of cx d' = mid_of cx d ->
  sv_nblock (d_sv d') = sv_nblock (d_sv d) -> blk_of cx d' = blk_of cx d ->
  drest_at a0segs m' (b_s cx) (r_of d') ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m' (dvF cx J d' s).
Proof.
  intros cx payload m m' J d d' s Hole PL AG HIN HOUT E1 E2 E3 E4 E5 E6 DR' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  unfold dmemL. cbn [dvF dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k] in *. rewrite E1, E2, E3, E4, E5, E6.
  assert (NH : forall x, ~ ((b_s cx + 68 <= x < b_s cx + 1092) \/ (b_s cx + 2124 <= x < b_s cx + 3152) \/ (b_s cx + 3196 <= x < b_s cx + 64036)) -> ~ Hole x)
    by (intros x N HX; exact (N (HIN x HX))).
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H1). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H2). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_u32arr_agree a0segs m m' _ _ H3). ag_sub AG. rewrite zw32_length in Hx by lia. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H4). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H5). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia| apply NH; lia]. }
  split; [exact DR'|].
  split. { apply (n_rw_cells_agree a0segs m m' _ _ H7). ag_sub AG. cbn [cells_size csize Nat.add] in Hx. split; [unfold dfp; lia|]. intros HX. destruct (HOUT x HX) as (N1 & _). apply N1. lia. }
  split. { apply (blk_agree m m' _ _ _ H8 AG). intros x Hx. split; [unfold dfp; tauto|]. intros HX. destruct (HOUT x HX) as (_ & _ & N3). exact (Hx N3). }
  apply (bytes_at_agree a0segs m m' _ _ H9). ag_sub AG. split; [unfold dfp; lia|]. intros HX. destruct (HOUT x HX) as (_ & N2 & _). apply N2. lia.
Qed.

(* [comment removed for export] *)
Ltac dr_xfer_one AG m m' :=
  lazymatch goal with
  | |- Z.of_nat _ = _ => first [assumption| rewrite ?zw32_length, ?zb8_length by lia; reflexivity]
  | |- u32arr _ m' ?a _ => match goal with H : u32arr _ m a ?ws |- _ =>
        first [ solve [apply (n_u32arr_agree a0segs m m' a ws H); ag_sub AG; split; [unfold dfp; lia| cbn [outside]; lia]] | idtac ] end
  | |- u8arr _ m' ?a _ => match goal with H : u8arr _ m a ?bs |- _ =>
        first [ solve [apply (n_u8arr_agree a0segs m m' a bs H); ag_sub AG; split; [unfold dfp; lia| cbn [outside]; lia]] | idtac ] end
  end.
Ltac dr_xfer D AG m m' :=
  destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14));
  unfold drest_at; repeat match goal with |- _ /\ _ => split end; dr_xfer_one AG m m'.

(* [comment removed for export] *)
Definition dsep (cx : bctx) : Prop :=
  forall x, b_s cx <= x < b_s cx + 64144 -> ~ (b_strm cx <= x < b_strm cx + 80) /\ ~ (b_src cx <= x < b_src cx + b_len cx) /\ outside (blk_ivls cx) x.

(* [comment removed for export] *)
Lemma dmx_inUse : forall cx payload (m m2 : mem) J d s iu, Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ outside [(b_s cx + 3196, b_s cx + 3196 + 256)] x) m m2 -> wmono a0segs m m2 ->
  dsep cx ->
  bytes_at a0segs m2 (b_s cx + 3196) (repeat z8 (Z.to_nat 256)) ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m2 (dvF cx J (d_set_inUse d (clear256 256 0 iu)) s).
Proof.
  intros cx payload m m2 J d s iu PL AG WM HOUT BY DM.
  apply (dmemL_rest cx payload m m2 J d _ s (fun x => b_s cx + 3196 <= x < b_s cx + 3452) PL); try reflexivity; try exact DM.
  - ag_sub AG. destruct Hx as [Hx1 Hx2]. split; [exact Hx1|]. cbn [outside]. lia.
  - intros x Hx. lia.
  - intros x Hx. apply HOUT. lia.
  - destruct DM as (_ & _ & _ & _ & _ & D & _).
    cbn [dvF dv_r] in D. dr_xfer D AG m m2.
    cbn [r_of r_inUse d_inUse d_set_inUse]. rewrite S0F_dec_U4A.zb8_clear256.
    cbn [r_of r_inUse] in A3, L3. destruct A3 as [_ W3]. split; [exact BY|].
    rewrite repeat_length. rewrite zb8_length_nat in W3. exact (wr_at_transport a0segs m m2 _ _ W3 WM).
Qed.

(* [comment removed for export] *)
Lemma dmx_unzftab : forall cx payload (m m2 : mem) J d s, Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ outside [(b_s cx + 68, b_s cx + 68 + 1024)] x) m m2 -> wmono a0segs m m2 ->
  dsep cx ->
  bytes_at a0segs m2 (b_s cx + 68) (repeat z8 (Z.to_nat 1024)) ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m2 (dvF cx J (d_set_unzftab d (clear256 256 0 (d_unzftab d))) s).
Proof.
  intros cx payload m m2 J d s PL AG WM HOUT BY DM.
  apply (dmemL_rest cx payload m m2 J d _ s (fun x => b_s cx + 68 <= x < b_s cx + 1092) PL); try reflexivity; try exact DM.
  - ag_sub AG. destruct Hx as [Hx1 Hx2]. split; [exact Hx1|]. cbn [outside]. lia.
  - intros x Hx. lia.
  - intros x Hx. apply HOUT. lia.
  - destruct DM as (_ & _ & _ & _ & _ & D & _).
    cbn [dvF dv_r] in D. dr_xfer D AG m m2.
    cbn [r_of r_unz d_unzftab d_set_unzftab]. rewrite S0F_dec_U7D.zw32_clear256.
    cbn [r_of r_unz] in A1, L1. destruct A1 as [_ W1]. rewrite zw32_length_nat in W1.
    split.
    + rewrite u32s_repeat_zero. exact BY.
    + rewrite repeat_length. exact (wr_at_transport a0segs m m2 _ _ W1 WM).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rows_lws (d : dst) (t : Z) : list word := firstn 258 (skipn (Z.to_nat (258 * t)) (zw32 (d_limit d) 1548)).
Definition rows_bws (d : dst) (t : Z) : list word := firstn 258 (skipn (Z.to_nat (258 * t)) (zw32 (d_base d) 1548)).
Definition rows_pws (d : dst) (t : Z) : list word := firstn 258 (skipn (Z.to_nat (258 * t)) (zw32 (d_perm d) 1548)).
Definition rows_lbs (d : dst) (t : Z) : list byte := firstn 258 (skipn (Z.to_nat (258 * t)) (zb8 (d_len d) 1548)).

Lemma dmx_rows_pre : forall cx payload (m : mem) J d s t, 0 <= t < 6 -> dmemL cx payload m (dvF cx J d s) ->
  u32arr a0segs m (b_s cx + 45436 + 1032 * t) (rows_lws d t) /\ length (rows_lws d t) = 258%nat /\
  u32arr a0segs m (b_s cx + 51628 + 1032 * t) (rows_bws d t) /\ length (rows_bws d t) = 258%nat /\
  u32arr a0segs m (b_s cx + 57820 + 1032 * t) (rows_pws d t) /\ length (rows_pws d t) = 258%nat /\
  u8arr a0segs m (b_s cx + 43888 + 258 * t) (rows_lbs d t) /\ length (rows_lbs d t) = 258%nat.
Proof.
  intros cx payload m J d s t Ht (_ & _ & _ & _ & _ & D & _). cbn [dvF dv_r] in D.
  destruct D as (_&_&_&_&_&_&_&_&_&(A10&_)&(A11&_)&(A12&_)&(A13&_)&_). cbn [r_of r_len r_lim r_base r_perm] in A10, A11, A12, A13.
  set (i0 := Z.to_nat (258 * t)). assert (Hi0 : Z.of_nat i0 = 258 * t) by (subst i0; lia).
  destruct (u32arr_split3 a0segs m _ (zw32 (d_limit d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) A11) as (_ & B11 & _ & _ & N11 & _).
  destruct (u32arr_split3 a0segs m _ (zw32 (d_base d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) A12) as (_ & B12 & _ & _ & N12 & _).
  destruct (u32arr_split3 a0segs m _ (zw32 (d_perm d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) A13) as (_ & B13 & _ & _ & N13 & _).
  destruct (u8arr_split3 a0segs m _ (zb8 (d_len d) 1548) i0 258 ltac:(rewrite zb8_length_nat; lia) A10) as (_ & B10 & _ & _ & N10 & _).
  unfold rows_lws, rows_bws, rows_pws, rows_lbs. fold i0.
  replace (b_s cx + 45436 + 1032 * t) with (b_s cx + 45436 + 4 * Z.of_nat i0) by lia.
  replace (b_s cx + 51628 + 1032 * t) with (b_s cx + 51628 + 4 * Z.of_nat i0) by lia.
  replace (b_s cx + 57820 + 1032 * t) with (b_s cx + 57820 + 4 * Z.of_nat i0) by lia.
  replace (b_s cx + 43888 + 258 * t) with (b_s cx + 43888 + Z.of_nat i0) by lia.
  split; [exact B11|]. split; [exact N11|]. split; [exact B12|]. split; [exact N12|]. split; [exact B13|]. split; [exact N13|]. split; [exact B10| exact N10].
Qed.

Lemma rows_len_ok : forall d t alpha mn mx, 0 <= t < 6 -> 1 <= alpha <= 258 ->
  (forall j, 0 <= j < alpha -> mn <= zget (d_len d) (258 * t + j) <= mx) ->
  (forall j, 0 <= j < alpha -> 1 <= zget (d_len d) (258 * t + j) <= 20) ->
  forall j, 0 <= j < alpha -> mn <= uv8 (rows_lbs d t) j <= mx.
Proof.
  intros d t alpha mn mx Ht Ha SCAN LALL j Hj. unfold rows_lbs. rewrite uv8_window by lia. rewrite Z2Nat.id by lia.
  rewrite S0F_dec_U7B.uv8_zb8 by (first [lia | pose proof (LALL j Hj); lia]). apply SCAN. exact Hj.
Qed.

Lemma dmx_rows : forall cx payload (m m' : mem) J d s t alpha mn mx (lws' bws' pws' : list word), Z.of_nat (length payload) = b_len cx ->
  agree_on (fun x => dfp cx x /\ outside [(b_s cx + 45436 + 1032 * t, b_s cx + 45436 + 1032 * t + 1032); (b_s cx + 51628 + 1032 * t, b_s cx + 51628 + 1032 * t + 1032);
                                          (b_s cx + 57820 + 1032 * t, b_s cx + 57820 + 1032 * t + 1032)] x) m m' ->
  dsep cx -> 1 <= alpha <= 258 -> 0 <= t < 6 -> (1 <= mn /\ mn <= mx <= 20) ->
  (forall j, 0 <= j < alpha -> mn <= zget (d_len d) (258 * t + j) <= mx) ->
  (forall j, 0 <= j < alpha -> 1 <= zget (d_len d) (258 * t + j) <= 20) ->
  u32arr a0segs m' (b_s cx + 45436 + 1032 * t) lws' -> length lws' = 258%nat ->
  u32arr a0segs m' (b_s cx + 51628 + 1032 * t) bws' -> length bws' = 258%nat ->
  u32arr a0segs m' (b_s cx + 57820 + 1032 * t) pws' -> length pws' = 258%nat ->
  (let '(limit, base, perm) := hb_create (sv32 (rows_lws d t)) (sv32 (rows_bws d t)) (sv32 (rows_pws d t)) (uv8 (rows_lbs d t)) mn mx alpha in
   ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258) ->
  dmemL cx payload m (dvF cx J d s) -> dmemL cx payload m' (dvF cx J (mt_rows t alpha d mn mx) s).
Proof.
  intros cx payload m m' J d s t alpha mn mx lws' bws' pws' PL AG HOUT Ha Ht Hmm SCAN LALL ARL' LNl' ARB' LNb' ARP' LNp' AGS DM.
  pose proof (mt_rows_bridge d t alpha mn mx Ha ltac:(lia) Hmm SCAN) as BRG. cbv zeta in BRG.
  pose proof (mt_rows_fields t alpha d mn mx) as FL. cbv zeta in FL.
  destruct (hbCreateDecodeTables (d_limit d) (d_base d) (d_perm d) (d_len d) (258 * t) mn mx alpha) as [[li ba] pe] eqn:HBD.
  destruct FL as (El & Eb & Ep & _).
  assert (ED : mt_rows t alpha d mn mx = d_set_perm (d_set_base (d_set_limit d li) ba) pe) by (unfold mt_rows; rewrite HBD; reflexivity).
  rewrite ED in El, Eb, Ep |- *. rewrite ED in BRG. cbn [d_limit d_base d_perm d_set_perm d_set_base d_set_limit] in BRG.
  apply (dmemL_rest cx payload m m' J d _ s
           (fun x => (b_s cx + 45436 + 1032 * t <= x < b_s cx + 45436 + 1032 * t + 1032) \/ (b_s cx + 51628 + 1032 * t <= x < b_s cx + 51628 + 1032 * t + 1032) \/
                     (b_s cx + 57820 + 1032 * t <= x < b_s cx + 57820 + 1032 * t + 1032)) PL); try reflexivity; try exact DM.
  - ag_sub AG. destruct Hx as [Hx1 Hx2]. split; [exact Hx1|]. cbn [outside]. lia.
  - intros x Hx. lia.
  - intros x Hx. apply HOUT. lia.
  - destruct DM as (_ & _ & _ & _ & _ & D & _). cbn [dvF dv_r] in D.
    set (i0 := Z.to_nat (258 * t)). assert (Hi0 : Z.of_nat i0 = 258 * t) by (subst i0; lia).
    (* [comment removed for export] *)
    pose proof (hb_create_cong (zrow (d_limit d) (258 * t)) (sv32 (rows_lws d t)) (zrow (d_base d) (258 * t)) (sv32 (rows_bws d t))
                  (zrow (d_perm d) (258 * t)) (sv32 (rows_pws d t)) (zrow (d_len d) (258 * t)) (uv8 (rows_lbs d t)) mn mx alpha) as CG.
    assert (CGl : cong32 (zrow (d_limit d) (258 * t)) (sv32 (rows_lws d t))).
    { intros i Hi. unfold zrow, rows_lws. fold i0. rewrite S0F_dec_U7B.sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGb : cong32 (zrow (d_base d) (258 * t)) (sv32 (rows_bws d t))).
    { intros i Hi. unfold zrow, rows_bws. fold i0. rewrite S0F_dec_U7B.sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGp : cong32 (zrow (d_perm d) (258 * t)) (sv32 (rows_pws d t))).
    { intros i Hi. unfold zrow, rows_pws. fold i0. rewrite S0F_dec_U7B.sv32_zw32_window, Hi0 by lia. reflexivity. }
    assert (CGn : forall j, 0 <= j < alpha -> zrow (d_len d) (258 * t) j = uv8 (rows_lbs d t) j).
    { intros j Hj. unfold zrow, rows_lbs. fold i0. rewrite uv8_window, Hi0 by lia. symmetry. apply S0F_dec_U7B.uv8_zb8; [lia|]. pose proof (LALL j Hj). lia. }
    specialize (CG CGl CGb CGp CGn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros j Hj; unfold zrow; pose proof (LALL j Hj); lia)).
    destruct (hb_create (zrow (d_limit d) (258 * t)) (zrow (d_base d) (258 * t)) (zrow (d_perm d) (258 * t)) (zrow (d_len d) (258 * t)) mn mx alpha) as [[lim bas] per] eqn:HCz.
    destruct (hb_create (sv32 (rows_lws d t)) (sv32 (rows_bws d t)) (sv32 (rows_pws d t)) (uv8 (rows_lbs d t)) mn mx alpha) as [[lim' bas'] per'] eqn:HCm.
    destruct CG as (CG1 & CG2 & CG3). destruct AGS as (AG1 & AG2 & AG3). destruct BRG as [BROW BFRM].
    (* [comment removed for export] *)
    pose proof D as D0.
    destruct D0 as (_&_&_&_&_&_&_&_&_&_&(T11&_)&(T12&_)&(T13&_)&_). cbn [r_of r_lim r_base r_perm] in T11, T12, T13.
    destruct (u32arr_split3 a0segs m _ (zw32 (d_limit d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) T11) as (LIMa & _ & LIMc & LNLa & _ & _).
    destruct (u32arr_split3 a0segs m _ (zw32 (d_base d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) T12) as (BASa & _ & BASc & LNBa & _ & _).
    destruct (u32arr_split3 a0segs m _ (zw32 (d_perm d) 1548) i0 258 ltac:(rewrite zw32_length_nat; lia) T13) as (PRMa & _ & PRMc & LNPa & _ & _).
    assert (XA : forall a ws, u32arr a0segs m a ws -> b_s cx + 45436 <= a -> a + 4 * Z.of_nat (length ws) <= b_s cx + 64012 ->
              (forall x, a <= x < a + 4 * Z.of_nat (length ws) ->
                 ~ ((b_s cx + 45436 + 1032 * t <= x < b_s cx + 45436 + 1032 * t + 1032) \/ (b_s cx + 51628 + 1032 * t <= x < b_s cx + 51628 + 1032 * t + 1032) \/
                    (b_s cx + 57820 + 1032 * t <= x < b_s cx + 57820 + 1032 * t + 1032))) -> u32arr a0segs m' a ws).
    { intros a ws H B0 B1 NH. apply (n_u32arr_agree a0segs m m' a ws H). ag_sub AG. split; [unfold dfp; lia|]. cbn [outside]. pose proof (NH x Hx). lia. }
    assert (LSK : forall (ws : list word), length ws = 1548%nat -> Z.of_nat (length (skipn (i0 + 258) ws)) = 1548 - 258 - 258 * t) by (intros ws E; rewrite length_skipn, E; lia).
    assert (LFS : forall (ws : list word), length ws = 1548%nat -> Z.of_nat (length (firstn i0 ws)) = 258 * t) by (intros ws E; rewrite firstn_length_le by lia; lia).
    pose proof (zw32_length_nat (d_limit d) 1548) as ZL1. pose proof (zw32_length_nat (d_base d) 1548) as ZL2. pose proof (zw32_length_nat (d_perm d) 1548) as ZL3.
    change (Z.to_nat 1548) with 1548%nat in ZL1, ZL2, ZL3.
    apply XA in LIMa; [| lia| rewrite (LFS _ ZL1); lia| intros x Hx; rewrite (LFS _ ZL1) in Hx; lia].
    apply XA in LIMc; [| lia| rewrite (LSK _ ZL1); lia| intros x Hx; rewrite (LSK _ ZL1) in Hx; lia].
    apply XA in BASa; [| lia| rewrite (LFS _ ZL2); lia| intros x Hx; rewrite (LFS _ ZL2) in Hx; lia].
    apply XA in BASc; [| lia| rewrite (LSK _ ZL2); lia| intros x Hx; rewrite (LSK _ ZL2) in Hx; lia].
    apply XA in PRMa; [| lia| rewrite (LFS _ ZL3); lia| intros x Hx; rewrite (LFS _ ZL3) in Hx; lia].
    apply XA in PRMc; [| lia| rewrite (LSK _ ZL3); lia| intros x Hx; rewrite (LSK _ ZL3) in Hx; lia].
    replace (b_s cx + 45436 + 1032 * t) with (b_s cx + 45436 + 4 * Z.of_nat i0) in ARL' by lia.
    replace (b_s cx + 51628 + 1032 * t) with (b_s cx + 51628 + 4 * Z.of_nat i0) in ARB' by lia.
    replace (b_s cx + 57820 + 1032 * t) with (b_s cx + 57820 + 4 * Z.of_nat i0) in ARP' by lia.
    clear XA.
    dr_xfer D AG m m'.
    + cbn [r_of r_lim d_limit d_set_perm d_set_base d_set_limit].
      eapply (u32arr_ext4 a0segs m' (b_s cx + 45436) (firstn i0 (zw32 (d_limit d) 1548) ++ lws' ++ skipn (i0 + 258) (zw32 (d_limit d) 1548)));
        [ apply u32arr_join3; [ exact LIMa | rewrite LNLa; exact ARL' | rewrite LNLa, LNl'; exact LIMc ]
        | apply (S0F_dec_U7B.splice_zw32 (d_limit d) li 1548 i0 lws' lim' ltac:(lia) LNl' AG1);
          [ intros i Hi; rewrite <- (CG1 i Hi), Hi0; destruct (BROW i Hi) as (Q1 & _ & _); rewrite Q1; reflexivity
          | intros j Hj Hjk; destruct (BFRM j ltac:(lia)) as (Q1 & _ & _); exact Q1 ] ].
    + cbn [r_of r_base d_limit d_base d_set_perm d_set_base d_set_limit].
      eapply (u32arr_ext4 a0segs m' (b_s cx + 51628) (firstn i0 (zw32 (d_base d) 1548) ++ bws' ++ skipn (i0 + 258) (zw32 (d_base d) 1548)));
        [ apply u32arr_join3; [ exact BASa | rewrite LNBa; exact ARB' | rewrite LNBa, LNb'; exact BASc ]
        | apply (S0F_dec_U7B.splice_zw32 (d_base d) ba 1548 i0 bws' bas' ltac:(lia) LNb' AG2);
          [ intros i Hi; rewrite <- (CG2 i Hi), Hi0; destruct (BROW i Hi) as (_ & Q2 & _); rewrite Q2; reflexivity
          | intros j Hj Hjk; destruct (BFRM j ltac:(lia)) as (_ & Q2 & _); exact Q2 ] ].
    + cbn [r_of r_perm d_limit d_base d_perm d_set_perm d_set_base d_set_limit].
      eapply (u32arr_ext4 a0segs m' (b_s cx + 57820) (firstn i0 (zw32 (d_perm d) 1548) ++ pws' ++ skipn (i0 + 258) (zw32 (d_perm d) 1548)));
        [ apply u32arr_join3; [ exact PRMa | rewrite LNPa; exact ARP' | rewrite LNPa, LNp'; exact PRMc ]
        | apply (S0F_dec_U7B.splice_zw32 (d_perm d) pe 1548 i0 pws' per' ltac:(lia) LNp' AG3);
          [ intros i Hi; rewrite <- (CG3 i Hi), Hi0; destruct (BROW i Hi) as (_ & _ & Q3); rewrite Q3; reflexivity
          | intros j Hj Hjk; destruct (BFRM j ltac:(lia)) as (_ & _ & Q3); exact Q3 ] ].
Qed.

End DECX.
