(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma lb_bytes_perm : forall L L', Permutation L L' -> lb_bytes L = lb_bytes L'.
Proof. induction 1; unfold lb_bytes in *; cbn [fold_right] in *; lia. Qed.
Lemma lb_big_perm : forall L L', Permutation L L' -> lb_big L = lb_big L'.
Proof. induction 1; unfold lb_big in *; cbn [fold_right] in *; lia. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section HH.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma chain_below_of_RHEAP : forall s L m0 LBx m c lo,
    hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) -> ERR_chain LBx m c -> hceil <= lo -> chain_below c lo.
  Proof.
    intros s L m0 LBx m c lo HP SUB (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & _) CE. unfold chain_below.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I2)) as R2. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I3)) as R3.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I4)) as R4. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as R5.
    unfold rblock_range in *. rewrite Z2 in R2. rewrite Z3 in R3. rewrite Z4 in R4. rewrite Z5 in R5. unfold ERRST_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma es_not_client : forall s SB LBN LB m0 m c ph SP X a,
    hs_RHEAP H s (SB ++ LBN ++ LB) m0 -> ERR_chain (LBN ++ LB) m c -> errph_delta ph LBN c -> hceil <= SP ->
    blk_addr (ec_es c) <= a < blk_addr (ec_es c) + ERRST_SIZE -> ~ xclient LB SP (X ++ errph_foot ph) a.
  Proof.
    intros s SB LBN LB m0 m c ph SP X a HP EC DL CE Hr [HC HXn]. hcb.
    destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (SUB2 : forall b, In b (LBN ++ LB) -> In b (SB ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB2 _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP) as ND2. unfold ERRST_SIZE in *.
    destruct HC as [K|[[K _]|(b & Hb & Hrb)]]; [lia| lia|].
    assert (NN : ~ (blk_id b <> blk_id (ec_es c))).
    { intros NE. pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ _ _ HP (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) NE) as DJ.
      rewrite Z5 in DJ. lia. }
    apply NN. intros EQid.
    pose proof (nodup_id_inj _ _ _ ND2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) EQid) as EQB. subst b.
    destruct ph as [|cq]; cbn [errph_delta errph_foot] in *.
    - destruct DL as (_ & _ & _ & FA). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FA)))) as IN5.
      assert (NDx : List.NoDup (map blk_id (LBN ++ LB))) by (rewrite map_app in ND2; eapply NoDup_app_remove_l; exact ND2).
      eapply (nodup_map_app_excl blk_id LBN LB (ec_es c)); [exact NDx| exact IN5| exact Hb].
    - destruct DL as [-> _]. apply HXn. apply rin_ivs_app. right. cbn. left. unfold ERRST_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Definition heapw4 (c : errchain) (lo spx : Z) (b0 : block) (iv : Z * Z) : Prop :=
    heapw c lo spx b0 iv \/ (RERRNO <= fst iv /\ snd iv <= RERRNO + 4).

  Lemma C4W_heapw4 : forall LBx L s m0 W m m' c x lo spx b0,
    C4W LBx m (ErrReady c) x -> hs_RHEAP H s L m0 -> (forall b, In b LBx -> In b L) ->
    In b0 L -> ~ In b0 LBx -> hceil <= lo ->
    munch W m m' -> wmono rsegs m m' -> Forall (heapw4 c lo spx b0) W ->
    C4W LBx m' (ErrReady c) x.
  Proof.
    intros LBx L s m0 W m m' c x lo spx b0 ((fb & MF & MV) & IM & GM & RL & [ES EC] & [CS [EX OL]]) HP SUB IB0 NB0 CEIL MU WM FW. hcb.
    pose proof EC as EC0. destruct EC as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB0) as RB0. unfold rblock_range in RB0. unfold ERRST_SIZE in *.
    assert (APART : forall d, In d LBx -> blk_size d <> 904 -> 0 <= blk_size d -> blk_addr d + blk_size d <= hceil ->
                    (blk_addr d + blk_size d <= 65536 \/ 3215360 <= blk_addr d) ->
                    forall A n, blk_addr d <= A -> A + n <= blk_addr d + blk_size d -> disjoint_from W A n).
    { intros d Hd SZ SZ0 DH DOFF A n HA1 HA2.
      pose proof (blocks_apart_by_size H HH _ _ _ _ _ HP (SUB _ Hd) (SUB _ I5) ltac:(rewrite Z5; exact SZ)) as D5. rewrite Z5 in D5.
      assert (D0 : blk_addr d + blk_size d <= blk_addr b0 \/ blk_addr b0 + blk_size b0 <= blk_addr d).
      { eapply (HH_RHEAP_blocks_disjoint H HH); [exact HP| apply SUB; exact Hd| exact IB0|]. intros EQ. apply NB0.
        rewrite <- (nodup_id_inj L d b0 (HH_RHEAP_blocks_nodup H HH _ _ _ HP) (SUB _ Hd) IB0 EQ). exact Hd. }
      clear - FW D5 D0 HA1 HA2 CEIL DH DOFF. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw4, heapw, ERRST_SIZE, RERRNO in K. cbn [fst snd] in K. lia. }
    assert (OFFI : forall A n, 65536 <= A -> A + n <= 3215360 -> (A + n <= RERRNO \/ RERRNO + 4 <= A) -> disjoint_from W A n).
    { intros A n H1 H2 H3. clear - FW RB5 RB0 H1 H2 H3 CEIL HCEILB. induction W as [|[wl wh] W IH]; [exact I|]. cbn. split; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw4, heapw, ERRST_SIZE in K. cbn [fst snd] in K. lia. }
    assert (FX : Forall off_libx W).
    { clear - FW RB5 RB0 CEIL HCEILB. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw4, heapw, ERRST_SIZE in K. cbn [fst snd] in K. unfold off_libx, IMG_LO, IMG_HI. cbn [fst snd]. lia. }
    pose proof (Forall_inv RR) as R2. pose proof (Forall_inv (Forall_inv_tail RR)) as R3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RR))) as R4. unfold rblock_range in R2, R3, R4.
    split; [exists fb; split; [eapply rw_cells_transport; [exact MF| exact MU| exact WM| apply OFFI; unfold A_mem_inited, RERRNO; cbn; lia]| exact MV]|].
    split; [unfold IMPL_mem in *; eapply rw_cells_transport; [exact IM| exact MU| exact WM| apply OFFI; unfold A_malloc_impl, RERRNO; cbn; lia]|].
    split; [unfold GOT_mem in *; eapply rw_cells_transport; [exact GM| exact MU| exact WM| apply OFFI; unfold A_got_CRYPTO_malloc, RERRNO; cbn; lia]|].
    split.
    { intros a Ha NS. unfold wa. rewrite MU; [apply RL; assumption|]. rewrite unsigned_lit by (unfold RELRO_LO, RELRO_HI in Ha; lia).
      eapply disjoint_outside; [apply (OFFI a 1); unfold RELRO_LO, RELRO_HI, RERRNO in *; lia| lia]. }
    split.
    - split; [eapply ERR_statics_munch; eassumption|].
      unfold ERR_chain, sa_cells. repeat match goal with |- _ /\ _ => split end; try assumption.
      + eapply rw_cells_transport; [exact K2| exact MU| exact WM|]. apply (APART _ I2); unfold O_MKEY_ERR; cbn; lia.
      + eapply rw_cells_transport; [exact K3| exact MU| exact WM|]. apply (APART _ I3); cbn; lia.
      + eapply rw_cells_transport; [exact K4| exact MU| exact WM|]. apply (APART _ I4); cbn; lia.
    - split; [eapply CTX_statics_munch; eassumption|]. split; [| exact OL].
      pose proof EX as (XI & XZ & XR & _). unfold rblock_range, MUTEX_SIZE in *.
      eapply EXLOCK_munch; [exact EX| exact MU| exact WM|]. apply (APART _ XI); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma heapw4_world : forall s L LBx m m' c x lo spx B b0 W,
    hs_RHEAP H s L m -> (forall b, In b LBx -> In b L) -> In b0 L -> ~ In b0 LBx -> C4W LBx m (ErrReady c) x ->
    hs_rauxv_ok H m B -> hceil <= lo -> lo <= spx -> spx <= B ->
    munch W m m' -> wmono rsegs m m' -> Forall (heapw4 c lo spx b0) W ->
    hs_RHEAP H s L m' /\ C4W LBx m' (ErrReady c) x /\ hs_rauxv_ok H m' B.
  Proof.
    intros s L LBx m m' c x lo spx B b0 W HP SUB IB0 NB0 CW AUX CEIL LS SB MU WM FW. hcb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP (SUB _ I5)) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP IB0) as RB0. unfold rblock_range in RB0. unfold ERRST_SIZE in *.
    split.
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU| exact WM|].
      clear - FW CEIL I5 Z5 SUB IB0. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
      pose proof (Forall_inv FW) as K. unfold heapw4, heapw, ERRST_SIZE in K. cbn [fst snd] in K. destruct K as [[K|[K|K]]|K].
      - left. cbn. lia.
      - right; right. exists (ec_es c). split; [apply SUB; exact I5|]. rewrite Z5. unfold ERRST_SIZE. cbn. lia.
      - right; right. exists b0. split; [exact IB0|]. cbn. lia.
      - right; left. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. cbn. lia. }
    split; [eapply C4W_heapw4; eassumption|].
    eapply (HH_rauxv_frame H HH); [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL.
    clear - FW CEIL LS SB RB5 RB0 HCEILB. induction W as [|[wl wh] W IH]; [constructor|]. constructor; [| apply IH; exact (Forall_inv_tail FW)].
    pose proof (Forall_inv FW) as K. unfold heapw4, heapw, ERRST_SIZE, RERRNO in K. cbn [fst snd] in K |- *. lia.
  Qed.
End HH.

(* [comment removed for export] *)
Lemma xpres_drop_nonclient : forall LB SP X Y m m',
  xpres LB SP (X ++ Y) m m' -> (forall a, rin_ivs Y a -> ~ xclient LB SP X a) -> xpres LB SP X m m'.
Proof.
  intros LB SP X Y m m' XP NC a Ha HC. apply XP; [exact Ha|]. destruct HC as [HC HX]. split; [exact HC|].
  intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (HX K)| exact (NC a K (conj HC HX))].
Qed.

End HCW.
