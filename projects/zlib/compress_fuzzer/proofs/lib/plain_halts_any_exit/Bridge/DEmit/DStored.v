(** * Bridge.DEmit.DStored — pair D13 of PAIRS.md: [deflate_stored] at [Z_FINISH], S5 vs RT.

    Level 0's block function, from a state with an empty queue (what
    compress_fuzzer's one [deflate(Z_FINISH)] call reaches straight after the
    zlib header and its flush), in the shape of group M's [dm_deflate_fast]:
    the same block state, [dst_rel] kept, and afterwards what the trailer
    pair (D9 [pair_deflate_trailer]) needs ([post_ok]).

    The parts: [DStKit] (the invariant [sti] and the kit), [DStTrip] (one
    trip and the loop, whose two fuels both suffice), [DStWin] (the window
    update and [high_water] after the loop), [DStTail] (the tail when the
    loop stopped without the last block).

    The S5 entry facts [st_inv] replace the published statement's [em_inv]
    (whose [ec_level] says [1 <= level], so it never holds at level 0).

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk
  RefDeflStored5 RefDeflStored6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush DTrStored DZHeader
  DStKit DStTrip DStWin DStTail.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MLz.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module S5' := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored5.
Module S6' := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored6.

(** S5's side at the entry: the queue empty and starting at 0, no bit
    pending, the output counters in range. *)
Record st_inv (s : DS.deflate_state) : Prop := mkStInv {
  sv_pend : DS.ds_pending s = 0;
  sv_pout : DS.ds_pending_out s = 0;
  sv_biv : DS.ds_bi_valid s = 0;
  sv_aout : 0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32;
  sv_tout : 0 <= DS.cs_total_out (DS.ds_strm s);
  sv_room : DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s)
            + arr_len (DS.ds_pending_buf s) < 2 ^ 64
}.

Lemma sti_entry : forall s t pre_out pre_in, dst_rel s t pre_out pre_in -> mt_inv t -> st_inv s ->
  DS.ds_sym_next s = 0 -> 0 <= RD.ls_blockstart (RD.d_ls t) -> RD.ls_insert (RD.d_ls t) <= 32768 ->
  sti s t pre_out pre_in.
Proof.
  intros s t pre_out pre_in Hrel Hmt Hsv Hsn Hbs0 Hins.
  pose proof (m_cfg_facts t Hmt) as Hc.
  destruct Hsv as [Hp Hpo Hbv Hao Hto Hroom].
  destruct Hmt as [Hlev Hcfg Hwr Hrb Hms Hfa Hsl Hwin Hma Hml Hbs Hhw Hslid Hinl Hpend].
  destruct Hms as [Hch Hws Hmd Hwz Hstr Hlk Hrm Hins0 Hwm Hhm].
  destruct Hslid as (slid & Hs0 & Hdone & _ & _ & _).
  pose proof (cf_w_size _ Hc) as Cws.
  assert (0 <= RC.zlen (RD.zs_in (RD.d_strm t))) by (unfold RC.zlen; lia).
  constructor; try assumption; try lia.
Qed.

(** From the invariant. *)
Theorem st_deflate_stored : forall s t pre_out pre_in, sti s t pre_out pre_in ->
  bs_of (snd (DB.deflate_stored s Z_FINISH)) = fst (RD.deflate_stored Z_FINISH t)
  /\ dst_rel (fst (DB.deflate_stored s Z_FINISH)) (snd (RD.deflate_stored Z_FINISH t)) pre_out pre_in
  /\ post_ok (fst (DB.deflate_stored s Z_FINISH)).
Proof.
  intros s t pre_out pre_in Si.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc) as (Ews & Epbs & _ & _ & _ & _ & _ & _ & Eai & Eao & _).
  pose proof (zlen_done_rel _ _ _ _ Hrel) as D0.
  pose proof Hrel as (_ & _ & _ & _ & _ & Hst). unfold strm_rel in Hst. cbv zeta in Hst.
  destruct Hst as (Hni & Hai & _).
  pose proof (cf_w_size _ Hc) as Cws. pose proof (cf_pbs _ Hc) as Cpbs.
  rewrite S6'.deflate_stored_eq1.
  unfold RD.deflate_stored. cbv zeta.
  replace (wrap32 (DB.MIN (DS.ds_pending_buf_size s - 5) (DS.ds_w_size s))) with 32768
    by (rewrite Epbs, Ews; reflexivity).
  rewrite Cpbs, Cws. change (RD.zmin (65536 - 5) 32768) with 32768.
  pose proof (st_loop (Z.to_nat (DS.cs_avail_out (DS.ds_strm s) + 1))
                (Z.to_nat (RD.zs_availout (RD.d_strm t) / 5) + 3) s t pre_out pre_in 32768 Si
                ltac:(lia) ltac:(rewrite <- Eao; lia)) as L.
  cbv zeta in L. revert L.
  destruct (DB.deflate_stored_loop (Z.to_nat (DS.cs_avail_out (DS.ds_strm s) + 1)) s Z_FINISH 32768)
    as [s1 last].
  destruct (RD.dst_loop (Z.to_nat (RD.zs_availout (RD.d_strm t) / 5) + 3) Z_FINISH 32768 t) as [last0 t1].
  cbn [fst snd]. intros (L1 & L2 & L3 & L4 & L5 & L6). subst last0.
  rewrite S6'.post_loop_eq.
  pose proof (si_rel _ _ _ _ L2) as Hrel1.
  destruct (rel_view _ _ _ _ Hrel1 (si_cfg _ _ _ _ L2)) as (_ & _ & _ & _ & _ & _ & _ & _ & Eai1 & _).
  pose proof (zlen_done_rel _ _ _ _ Hrel1) as D1.
  assert (Z1 : 0 <= RC.zlen (RD.zs_done (RD.d_strm t))) by (unfold RC.zlen; lia).
  assert (Z2 : 0 <= RC.zlen (RD.zs_in (RD.d_strm t1))) by (unfold RC.zlen; lia).
  assert (Z3 : 0 <= RC.zlen pre_in) by (unfold RC.zlen; lia).
  rewrite (wrap32_id (DS.cs_avail_in (DS.ds_strm s) - DS.cs_avail_in (DS.ds_strm s1))) by lia.
  rewrite Eai, Eai1.
  pose proof (pair_wupd s1 t1 pre_out pre_in
                (RC.zlen (RD.zs_in (RD.d_strm t)) - RC.zlen (RD.zs_in (RD.d_strm t1))) (RD.d_cfg t)
                L2 Cws ltac:(lia) ltac:(lia)) as W.
  pose proof (pair_hw _ _ _ _ W) as H.
  destruct (Z.eqb_spec last 0) as [E0|E0].
  - subst last. cbn [negb Z.eqb]. exact (pair_tail _ _ _ _ _ H Hc).
  - rewrite S6'.post_hw_eq.
    replace (negb (last =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact E0).
    cbn [fst snd bs_of].
    split; [reflexivity|]. split; [exact (si_rel _ _ _ _ H) | exact (sti_post_ok _ _ _ _ H)].
Qed.

(** Pair D13: compress_fuzzer's level-0 [deflate(Z_FINISH)] call, from the
    state after the zlib header (no symbol, an empty queue at 0, block start
    and [insert] in range). *)
Theorem br_deflate_stored : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t -> st_inv s ->
  RC.dg_level (RD.d_cfg t) = 0 -> DS.ds_lookahead s = 0 -> DS.ds_sym_next s = 0 ->
  0 <= RD.ls_blockstart (RD.d_ls t) -> RD.ls_insert (RD.d_ls t) <= 32768 ->
  bs_of (snd (DB.deflate_stored s Z_FINISH)) = fst (RD.deflate_stored Z_FINISH t)
  /\ dst_rel (fst (DB.deflate_stored s Z_FINISH)) (snd (RD.deflate_stored Z_FINISH t)) pre_out pre_in
  /\ post_ok (fst (DB.deflate_stored s Z_FINISH)).
Proof.
  intros s t pre_out pre_in Hrel Hmt Hsv _ _ Hsn Hbs0 Hins.
  apply st_deflate_stored. exact (sti_entry s t pre_out pre_in Hrel Hmt Hsv Hsn Hbs0 Hins).
Qed.

(** The same in the shape of [DStoredIface.br_deflate_stored] (its [st_inv] is
    the conjunction below, its last three conclusions are [post_ok]), with the
    window still empty: [strstart = block_start = 0], which gives the block
    start and [insert] ranges the pair needs (an [mt_inv] state alone allows
    [32768 < insert], where S5's [wrap32 (w_size - insert)] and RT's
    [w_size - insert] part in the window update). *)
Theorem br_deflate_stored_iface : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> mt_inv t ->
  (DS.ds_pending s = 0 /\ DS.ds_pending_out s = 0 /\ DS.ds_bi_valid s = 0
   /\ 0 <= DS.cs_avail_out (DS.ds_strm s) < 2 ^ 32 /\ 0 <= DS.cs_total_out (DS.ds_strm s)
   /\ DS.cs_total_out (DS.ds_strm s) + DS.cs_avail_out (DS.ds_strm s) + arr_len (DS.ds_pending_buf s) < 2 ^ 64) ->
  RC.dg_level (RD.d_cfg t) = 0 -> DS.ds_lookahead s = 0 -> DS.ds_sym_next s = 0 ->
  DS.ds_strstart s = 0 -> DS.ds_block_start s = 0 ->
  bs_of (snd (DB.deflate_stored s Z_FINISH)) = fst (RD.deflate_stored Z_FINISH t)
  /\ dst_rel (fst (DB.deflate_stored s Z_FINISH)) (snd (RD.deflate_stored Z_FINISH t)) pre_out pre_in
  /\ DS.ds_sym_next (fst (DB.deflate_stored s Z_FINISH)) = 0
  /\ fp_ok (fst (DB.deflate_stored s Z_FINISH))
  /\ (DS.cs_avail_out (DS.ds_strm (fst (DB.deflate_stored s Z_FINISH))) <> 0 ->
      room (fst (DB.deflate_stored s Z_FINISH)) 10).
Proof.
  intros s t pre_out pre_in Hrel Hmt (Hp & Hpo & Hbv & Hao & Hto & Hroom) Hlev Hla Hsn Hss0 Hbs0.
  pose proof Hrel as (_ & Hlz & _).
  pose proof (lzr_ss _ _ Hlz) as Ess. pose proof (lzr_bs _ _ Hlz) as Ebs.
  pose proof (RK.mi_ins _ (mt_ms _ Hmt)) as Hins.
  destruct (br_deflate_stored s t pre_out pre_in Hrel Hmt (mkStInv s Hp Hpo Hbv Hao Hto Hroom)
              Hlev Hla Hsn ltac:(lia) ltac:(lia)) as (A & B & C & D & E).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D | exact E].
Qed.

Print Assumptions br_deflate_stored.
Print Assumptions br_deflate_stored_iface.
