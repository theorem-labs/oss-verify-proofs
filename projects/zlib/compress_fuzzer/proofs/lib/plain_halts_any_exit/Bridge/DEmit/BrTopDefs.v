(** * Bridge.DEmit.BrTopDefs — helpers for group D's top: the block driver (D8), the deflate
    entry (D7) and the [BrCompressCall] assembly.

    - frames: [dst_rel] survives S5's [set_status] / [set_last_flush] against RT's
      [setD_status] / [setD_lastflush]; [strm_rel] reads the two streams only;
    - the pairs' S5 side conditions from S5's own safety invariant [DC] (RefDeflSafeI1):
      [dc_room] (room in the queue), [dc_bits] (the bit buffer, the queue below the symbol
      area), [fp_ok_of_DC] (BrFlush's integer premises), [st_inv_of_DC] (D13's level-0
      invariant) and [em_inv_of_DC] (group D's emission invariant, through S5's
      [RefDeflSafeLF.DC_fb_entry]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate
  RefDeflateRel RefDeflSafeG RefDeflSafeI1 RefDeflSafeLF RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DStoredIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SI1 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI1.
Module SLF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.
Module SFB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeFB.
Module SG := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeG.
Module RRel := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflateRel.

(** Split every conjunction on both sides and match the pieces (a hypothesis is tried before
    [split], which would also introduce the binders of a [forall] conjunct). *)
Ltac rel_close :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat first [assumption | reflexivity | split].

Ltac rel_unfold :=
  unfold dst_rel, geom_rel, lz_rel, bw_rel, pend_rel, sym_rel, tree_rel, strm_rel, DS.sym_buf_get in *;
  cbv zeta in *;
  cbn [RD.setD_status RD.setD_lastflush RD.d_cfg RD.d_status RD.d_lastflush RD.d_wrap RD.d_ts RD.d_ls
       RD.d_strm].

(* ------------------------------------------------------------------------- *)
(* 1.  Frames                                                                *)
(* ------------------------------------------------------------------------- *)

(* The two values are separate arguments: S5's and RT's state constants are distinct names. *)
Lemma dst_rel_set_status : forall s t pre_out pre_in v v', v = v' ->
  dst_rel s t pre_out pre_in -> dst_rel (DS.set_status s v) (RD.setD_status v' t) pre_out pre_in.
Proof. intros s t pre_out pre_in v v' <- H. rel_unfold. autorewrite with s5f_status. rel_close. Qed.

Lemma dst_rel_set_last_flush : forall s t pre_out pre_in v v', v = v' ->
  dst_rel s t pre_out pre_in -> dst_rel (DS.set_last_flush s v) (RD.setD_lastflush v' t) pre_out pre_in.
Proof. intros s t pre_out pre_in v v' <- H. rel_unfold. autorewrite with s5f_last_flush. rel_close. Qed.

Lemma mt_inv_set_status : forall t v, mt_inv t -> mt_inv (RD.setD_status v t).
Proof. intros t v H. apply (mt_inv_frame t); first [reflexivity | exact H]. Qed.

Lemma mt_inv_set_lastflush : forall t v, mt_inv t -> mt_inv (RD.setD_lastflush v t).
Proof. intros t v H. apply (mt_inv_frame t); first [reflexivity | exact H]. Qed.

Lemma strm_rel_congr : forall s s' t t' pre_out pre_in,
  DS.ds_strm s' = DS.ds_strm s -> RD.d_strm t' = RD.d_strm t ->
  strm_rel s t pre_out pre_in -> strm_rel s' t' pre_out pre_in.
Proof. intros s s' t t' pre_out pre_in Es Et H. unfold strm_rel in *. cbv zeta in *. rewrite Es, Et. exact H. Qed.

Lemma dst_rel_strm : forall s t pre_out pre_in, dst_rel s t pre_out pre_in -> strm_rel s t pre_out pre_in.
Proof. intros s t pre_out pre_in (_ & _ & _ & _ & _ & H). exact H. Qed.

(** The [geom_rel] conjuncts the top reads. *)
Lemma dst_rel_geom : forall s t pre_out pre_in, dst_rel s t pre_out pre_in ->
  DS.ds_level s = RC.dg_level (RD.d_cfg t) /\ DS.ds_status s = RD.d_status t
  /\ DS.ds_wrap s = RD.d_wrap t /\ DS.ds_last_flush s = RD.d_lastflush t.
Proof. intros s t pre_out pre_in (H & _). unfold geom_rel in H. cbv zeta in H. rel_close. Qed.

(** The stream conjuncts the top reads. *)
Lemma dst_rel_avail : forall s t pre_out pre_in, dst_rel s t pre_out pre_in ->
  RD.zs_availout (RD.d_strm t) = DS.cs_avail_out (DS.ds_strm s)
  /\ Chunk.zlen (RD.zs_in (RD.d_strm t)) = DS.cs_avail_in (DS.ds_strm s).
Proof.
  intros s t pre_out pre_in H. apply dst_rel_strm in H. unfold strm_rel in H. cbv zeta in H.
  destruct H as (_ & Ha & _ & _ & Hin & _ & _ & Hao & _).
  split; [exact Hao|]. rewrite <- Hin.
  pose proof (arr_slice_length (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s))
                (DS.cs_avail_in (DS.ds_strm s))) as L.
  unfold zlength in L. unfold Chunk.zlen. lia.
Qed.

Lemma dst_rel_symnext : forall s t pre_out pre_in, dst_rel s t pre_out pre_in ->
  DS.ds_sym_next s = RT.ts_symnext (RD.d_ts t).
Proof. intros s t pre_out pre_in (_ & _ & _ & (H & _) & _). exact H. Qed.

Lemma dst_rel_bivalid : forall s t pre_out pre_in, dst_rel s t pre_out pre_in ->
  DS.ds_bi_valid s = ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts t)).
Proof. intros s t pre_out pre_in (_ & _ & (_ & _ & H) & _). exact H. Qed.

(** With an empty S5 queue, RT's pending list is empty. *)
Lemma dst_rel_pending0 : forall s t pre_out pre_in, dst_rel s t pre_out pre_in -> DS.ds_pending s = 0 ->
  ZBitsOut.bw_out (RT.ts_bw (RD.d_ts t)) = [].
Proof.
  intros s t pre_out pre_in (_ & _ & (Hp & _) & _) E. destruct Hp as (_ & _ & _ & Hs).
  rewrite <- Hs, E. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The pairs' S5 side conditions from S5's safety invariant              *)
(* ------------------------------------------------------------------------- *)

(** An empty queue starts at 0 and has the whole pending buffer (at least 8192 bytes). *)
Lemma dc_room : forall c0 s k, SI1.DC c0 s -> DS.ds_pending s = 0 -> 0 <= k <= 8192 -> room s k.
Proof.
  intros c0 s k [[D X] _] Hp Hk. pose proof (SG.dwf_sizes s D) as (_ & _ & Sl & _).
  split; [exact (SI1.dx_pout0 _ X Hp)|]. rewrite Hp, (RRel.df_bl _ D). lia.
Qed.

(** The bit buffer and the queue against the symbol area (the live-symbols trailer's premises). *)
Lemma dc_bits : forall c0 s, SI1.DC c0 s -> DS.ds_pending s = 0 ->
  0 <= DS.ds_bi_valid s <= 16 /\ DS.ds_pending s + 10 <= DS.ds_lit_bufsize s.
Proof.
  intros c0 s [[D _] _] Hp. pose proof (SG.dwf_sizes s D) as (_ & _ & Sl & _).
  destruct (RRel.df_bi _ D) as [Hb _]. lia.
Qed.

(** The output counts: [total_out + avail_out] is the call's, which leaves room. *)
Lemma dc_out : forall c0 s,
  SI1.C0OK c0 -> SI1.DC c0 s -> DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 ->
  0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32 /\ 0 <= DS.cs_total_out (DS.ds_strm s)
  /\ DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s) + arr_len (DS.ds_pending_buf s) < 2 ^ 64
  /\ arr_len (DS.ds_pending_buf s) <= 2 ^ 17.
Proof.
  intros c0 s HC0 HDC Hroom.
  pose proof HDC as [[D _] V]. pose proof (SG.dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (RRel.df_bl _ D) as Hbl.
  pose proof (SI1.sv_out _ _ V) as Ho. pose proof (SI1.sv_tout _ _ V) as Ht.
  pose proof (SI1.sv_aout _ _ V) as Ha.
  pose proof (SI1.c0_out _ HC0) as E0. pose proof (SI1.c0_tout _ HC0) as T0. pose proof (SI1.c0_aout _ HC0) as A0.
  rewrite E0 in Ho, Ht. unfold SI1.zlen in Ho, Ht. cbn [length Z.of_nat] in Ho, Ht.
  rewrite Z.sub_0_r in Ht. rewrite wrap64_id in Ht by lia.
  lia.
Qed.

Lemma fp_ok_of_DC : forall c0 s,
  SI1.C0OK c0 -> SI1.DC c0 s -> DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 -> fp_ok s.
Proof.
  intros c0 s HC0 HDC Hroom. destruct (dc_out c0 s HC0 HDC Hroom) as (A & B & C & D).
  unfold fp_ok. lia.
Qed.

(** D13's level-0 invariant at an empty queue with an empty bit buffer. *)
Lemma st_inv_of_DC : forall c0 s,
  SI1.C0OK c0 -> SI1.DC c0 s -> DS.ds_pending s = 0 -> DS.ds_bi_valid s = 0 ->
  DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 ->
  DStoredIface.st_inv s.
Proof.
  intros c0 s HC0 HDC Hp Hbv Hroom. destruct (dc_out c0 s HC0 HDC Hroom) as (A & B & C & _).
  destruct (dc_room c0 s 0 HDC Hp ltac:(lia)) as [Hpo _].
  unfold DStoredIface.st_inv. split; [exact Hp|]. split; [exact Hpo|]. split; [exact Hbv|].
  split; [exact A|]. split; [exact B | exact C].
Qed.

Lemma dmode_pos : forall s, 1 <= DS.ds_level s -> SI1.dmode s <> 0.
Proof.
  intros s H. unfold SI1.dmode.
  destruct (Z.eqb_spec (DS.ds_level s) 0) as [E|E]; [lia|].
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

(** Group D's emission invariant at an empty queue and an empty symbol buffer, levels 1-9. *)
Lemma em_inv_of_DC : forall c0 s,
  SI1.C0OK c0 -> SI1.DC c0 s -> DS.ds_pending s = 0 -> DS.ds_sym_next s = 0 -> 1 <= DS.ds_level s ->
  DS.cs_total_out c0 + DS.cs_avail_out c0 + 2 ^ 17 < 2 ^ 64 ->
  em_inv s.
Proof.
  intros c0 s HC0 HDC Hp Hsn Hl Hroom.
  pose proof (SLF.DC_fb_entry c0 s 0 HC0 HDC Hp (dmode_pos s Hl) ltac:(lia)) as F.
  destruct (dc_out c0 s HC0 HDC Hroom) as (_ & _ & C & _).
  destruct F.
  split; [constructor; try assumption; lia | lia].
Qed.

Print Assumptions em_inv_of_DC.
Print Assumptions st_inv_of_DC.
Print Assumptions dst_rel_set_status.
