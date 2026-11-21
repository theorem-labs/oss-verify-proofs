(** * Bridge.DEmit.BrDispatch — pair D12 of PAIRS.md: the compression-function dispatch, S5 vs RT,
    at compress_fuzzer's [Z_FINISH].

    S5's [run_compress_func] and RT's [dispatch] pick the same block function: level 0 is
    [deflate_stored]; strategy 0 (compress_fuzzer's, [DMatchDefs.cf_geom]) rules out
    [deflate_huff] and [deflate_rle] (pair D16: not taken); levels 1-3 are [deflate_fast] and
    4-9 [deflate_slow] (RT reads [cfg_func level]).  The three block pairs are group M's
    [dm_deflate_fast] / [dm_deflate_slow] and a worker's [DStoredIface.br_deflate_stored]
    (D13), whose S5 precondition [blk_pre] this file names per level. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DStoredIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** compress_fuzzer's strategy is 0. *)
Lemma mt_strategy : forall t, mt_inv t -> RC.dg_strategy (RD.d_cfg t) = 0.
Proof. intros t H. rewrite (mt_cfg _ H). reflexivity. Qed.

(** The S5 invariant the block function of a level needs: D13's at level 0 (with the window
    still empty, [strstart = block_start = 0], and no symbols), group D's emission invariant
    otherwise. *)
Definition blk_pre (level : Z) (s : DS.deflate_state) : Prop :=
  if Z.eqb level 0 then DStoredIface.st_inv s /\ DS.ds_lookahead s = 0 /\ DS.ds_sym_next s = 0
                        /\ DS.ds_strstart s = 0 /\ DS.ds_block_start s = 0
  else em_inv s.

(** What the trailer pair of a level needs afterwards: D13 keeps the symbol buffer empty
    (for [DZHeader.pair_deflate_trailer]); M's pairs keep [mt_inv], whose [wrap = 1] the
    live-symbols trailer ([DZTrailLive]) asks for. *)
Definition blk_post (level : Z) (s : DS.deflate_state) (t : RD.DSt) : Prop :=
  if Z.eqb level 0 then DS.ds_sym_next s = 0 else mt_inv t.

Theorem br_dispatch : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t -> blk_pre (RC.dg_level (RD.d_cfg t)) s ->
  bs_of (snd (SDfl.run_compress_func s 4)) = fst (RD.dispatch 4 t)
  /\ dst_rel (fst (SDfl.run_compress_func s 4)) (snd (RD.dispatch 4 t)) pre_out pre_in
  /\ blk_post (RC.dg_level (RD.d_cfg t)) (fst (SDfl.run_compress_func s 4)) (snd (RD.dispatch 4 t)).
Proof.
  intros s t pre_out pre_in Hrel Hmt.
  pose proof Hrel as (Hg & _). unfold geom_rel in Hg. cbv zeta in Hg. destruct Hg as (Hlev & Hstr & _).
  pose proof (mt_level _ Hmt) as HL. pose proof (mt_strategy _ Hmt) as Hs0.
  unfold blk_pre, blk_post. unfold SDfl.run_compress_func, RD.dispatch, RC.cfg_func.
  rewrite Hlev, Hstr, Hs0.
  destruct (Z.eqb_spec (RC.dg_level (RD.d_cfg t)) 0) as [E0|E0]; intros Hinv.
  - destruct Hinv as (Hst & Hla & Hsn & Hss & Hbs).
    destruct (DStoredIface.br_deflate_stored s t pre_out pre_in Hrel Hmt Hst E0 Hla Hsn Hss Hbs) as (A & B & C & _).
    split; [exact A|]. split; [exact B | exact C].
  - destruct (Z.leb_spec (RC.dg_level (RD.d_cfg t)) 3) as [L3|L3].
    + destruct (dm_deflate_fast s t pre_out pre_in 4 Hrel Hmt Hinv ltac:(lia)) as (A & B & C & _).
      split; [exact A|]. split; [exact B | exact C].
    + destruct (dm_deflate_slow s t pre_out pre_in 4 Hrel Hmt Hinv ltac:(lia)) as (A & B & C & _).
      split; [exact A|]. split; [exact B | exact C].
Qed.

Print Assumptions br_dispatch.
