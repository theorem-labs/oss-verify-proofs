(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim Stdio ZHarness.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import F_fwritex Z_ikit Z_infl_defs Z_infl_defs2 Z_updwin Zlib_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma izs_of_pub : forall m L c z (p1 p2 : list byte),
  rw_cells psegs m (il_S L) (zs_pub (il_NI L + ic_next_in c) (ic_avail_in c) (ic_total_in c) (il_NO L + ic_next_out c) (ic_avail_out c) (ic_total_out c) p1 p2) ->
  izq m L z -> zs_msg z = ic_msg c -> zs_adler z = ic_adler c -> izs m L c.
Proof.
  intros m L c z p1 p2 PUB (dt & p3 & resv & PRIV) E1 E2. exists p1, p2, dt, p3, resv.
  unfold izs_call_cells. apply (proj2 (rw_cells_app psegs m _ _ _)). split.
  - exact PUB.
  - rewrite <- E1, <- E2. exact PRIV.
Qed.

Lemma izs_to_pub : forall m L c, izs m L c ->
  (exists p1 p2, rw_cells psegs m (il_S L) (zs_pub (il_NI L + ic_next_in c) (ic_avail_in c) (ic_total_in c) (il_NO L + ic_next_out c) (ic_avail_out c) (ic_total_out c) p1 p2))
  /\ izq m L (zstrm_of_icall c).
Proof.
  intros m L c (p1 & p2 & dt & p3 & resv & H). unfold izs_call_cells in H. apply (proj1 (rw_cells_app psegs m _ _ _)) in H. destruct H as [H1 H2].
  split; [exists p1, p2; exact H1|]. exists dt, p3, resv. exact H2.
Qed.

Lemma IST_setw : forall m L s A, is_window_blk s = None -> IST m L s -> IST m (il_setw L A) s.
Proof.
  intros m L s A HB [GA GT Gl Gw Gc Gwin ARRS LAY]. constructor; try assumption.
  - unfold isA, isA_cells in *. rewrite HB in *. exact GA.
  - unfold iwin. rewrite HB. exact I.
  - unfold ilay_ok in *. destruct LAY as [L1 _]. split; [exact L1|]. intros NE. exfalso. apply NE. exact HB.
Qed.
Lemma izs_setw : forall m L c A, izs m L c -> izs m (il_setw L A) c.
Proof. intros m L c A H. exact H. Qed.

Lemma agree_iv : forall LBx SP m1 m2 lo hi, rheap_pres LBx SP m1 m2 -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> rclient_addr LBx SP a) -> Z_dview.agree_on lo hi m1 m2.
Proof. intros LBx SP m1 m2 lo hi H Hlo Hhi HC a Ha. apply H; [lia| apply HC; exact Ha]. Qed.

Lemma in_block_iv : forall LBx (b : block) a, In b LBx -> blk_addr b <= a < blk_addr b + blk_size b -> in_block LBx a.
Proof. intros LBx b a Hb Ha. exists b. split; assumption. Qed.

Lemma imem_heap_pres : forall (X : ictx) s c r put LBx SPx m1 m2 (bs bc bu : block),
  rheap_pres LBx SPx m1 m2 ->
  SPx <= bv_unsigned (ix_sp X) + -224 -> bv_unsigned (ix_sp X) <= il_S (ix_L X) -> il_S (ix_L X) + 112 < 2^63 -> 0 <= SPx ->
  In bs LBx -> blk_addr bs = il_As (ix_L X) -> blk_size bs = 7176 -> 0 < il_As (ix_L X) -> il_As (ix_L X) + 7176 < 2^63 ->
  In bc LBx -> blk_addr bc <= il_NI (ix_L X) -> il_NI (ix_L X) + arr_len (ix_input X) <= blk_addr bc + blk_size bc -> 0 < il_NI (ix_L X) -> blk_addr bc + blk_size bc < 2^63 ->
  In bu LBx -> blk_addr bu <= il_NO (ix_L X) -> il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)) <= blk_addr bu + blk_size bu -> 0 < il_NO (ix_L X) -> blk_addr bu + blk_size bu < 2^63 ->
  0 <= arr_len (ix_input X) -> 0 <= put <= Z.of_nat (length (ix_rest0 X)) ->
  is_window_blk s = None ->
  iframeL X r m1 -> IREP m1 (ix_L X) s c -> iin m1 X -> iout m1 (ix_L X) (ix_rest0 X) c put ->
  iframeL X r m2 /\ IREP m2 (ix_L X) s c /\ iin m2 X /\ iout m2 (ix_L X) (ix_rest0 X) c put.
Proof.
  intros X s c r put LBx SPx m1 m2 bs bc bu HP SP1 SP2 S63 SP0 Hbs Ebs1 Ebs2 As0 As63 Hbc Ebc1 Ebc2 NI0 Bc63 Hbu Ebu1 Ebu2 NO0 Bu63 RIN RPUT HB (retw & jf & FRM) [ZS ST] IN OUT.
  assert (STKC : forall lo hi, SPx <= lo -> hi < 2^63 -> Z_dview.agree_on lo hi m1 m2).
  { intros lo hi H1 H2. apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. left. lia. }
  split; [|split; [|split]].
  - exists retw, jf. eapply Z_dview.rw_cells_agree; [exact FRM|]. apply STKC; [lia|].
    unfold iframe_cells. cbn [cells_size csize Nat.add]. lia.
  - split.
    + eapply izs_agree; [exact ZS|]. apply STKC; lia.
    + eapply IST_agree; [exact ST|]. split.
      * apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bs); [exact Hbs| lia].
      * intros NE. exfalso. apply NE. exact HB.
  - unfold iin in *. unfold u8ro in *. eapply Z_dview.bytes_at_agree; [exact IN|]. rewrite av8_length.
    apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bc); [exact Hbc| lia].
  - unfold iout in *. eapply Z_dview.u8arr_agree; [exact OUT|]. rewrite iout_bytes_length by lia.
    apply (agree_iv LBx SPx); [exact HP| lia| lia|]. intros a Ha. right; right. apply (in_block_iv _ bu); [exact Hbu| lia].
Qed.

Lemma IREPq_relay : forall m L0 s z NI NO, IREPq m L0 s z -> IREPq m (Z_irep.mkIL (il_S L0) (il_As L0) (il_Aw L0) NI NO) s z.
Proof.
  intros m [S0 As0 Aw0 NI0 NO0] s z NI NO [(dt & p3 & resv & HZ) [GA GT Gl Gw Gc Gwin ARRS LAY]].
  split; [exists dt, p3, resv; exact HZ|]. constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY].
Qed.
