(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_KitH ECH_Rep ECH_C0_stmt ECH_C2_stmt
     ECH_LibState ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C7_stmt ECH_C14_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition idsdisj (X Y : list block) : Prop := forall b b', In b X -> In b' Y -> blk_id b <> blk_id b'.
Lemma nd_app : forall X Y, List.NoDup (map blk_id (X ++ Y)) -> idsdisj X Y /\ List.NoDup (map blk_id Y).
Proof.
  intros X Y ND. split; [intros b b' Hb Hb'; eapply nodup_ids_app_ne; eassumption|].
  rewrite map_app in ND. eapply NoDup_app_remove_l. exact ND.
Qed.
Lemma idsdisj_app_r : forall X Y Z, idsdisj X (Y ++ Z) -> idsdisj X Y /\ idsdisj X Z.
Proof. intros X Y Z D. split; intros b b' Hb Hb'; apply D; [exact Hb| apply in_or_app; left; exact Hb'| exact Hb| apply in_or_app; right; exact Hb']. Qed.
Lemma idsdisj_cons_r : forall X y Z, idsdisj X (y :: Z) -> idsdisj X [y] /\ idsdisj X Z.
Proof. intros X y Z D. apply (idsdisj_app_r X [y] Z). exact D. Qed.
Lemma idsdisj_sym : forall X Y, idsdisj X Y -> idsdisj Y X.
Proof. intros X Y D b b' Hb Hb' E. exact (D b' b Hb' Hb (eq_sym E)). Qed.
Lemma idsdisj_sub_r : forall X Y Y', idsdisj X Y -> (forall b, In b Y' -> In b Y) -> idsdisj X Y'.
Proof. intros X Y Y' D S b b' Hb Hb'. apply D; [exact Hb| apply S; exact Hb']. Qed.
Lemma idsdisj_notin : forall X Y b, idsdisj X Y -> In b X -> ~ In b Y.
Proof. intros X Y b D Hb K. exact (D b b Hb K eq_refl). Qed.
Lemma idsdisj_notin' : forall X Y b, idsdisj X Y -> In b Y -> ~ In b X.
Proof. intros X Y b D Hb K. exact (D b b K Hb eq_refl). Qed.

(* [comment removed for export] *)
Lemma errph_nonneg : forall eph, 0 <= errph_bytes eph /\ 0 <= errph_cnt eph /\ 0 <= errph_big eph.
Proof. intros [|c]; cbn [errph_bytes errph_cnt errph_big]; unfold ERRINIT_BYTES, ERRINIT_CNT, ERRINIT_BIG; lia. Qed.
Lemma readcfg_stack_lo : forall M, 11136 <= READCFG_STACK M.
Proof. intros M. unfold READCFG_STACK, FR_OSSL_ECHSTORE_read_echconfiglist, FR_ech_read_priv_echconfiglist, RREALLOC_STACK, RMALLOC_STACK. lia. Qed.
Lemma readcfg_stack_ready : forall M f' x E' v',
  READCFG_STACK (mkMID f' (CtxReady x) (mid_err M) E' v') <= READCFG_STACK M.
Proof.
  intros [f [|b] eph E v] f' x E' v'; unfold READCFG_STACK, mid_stack; cbn [mid_ctx mid_err ctxph_stack]; [| lia].
  unfold GETDEFCTX_STACK, CTXINIT_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context, RREALLOC_STACK, RMALLOC_STACK. lia.
Qed.
Lemma membio_blocks_facts : forall a R,
  lb_bytes (blocks_MEMBIO a R) = MEMBIO_BYTES /\ length (blocks_MEMBIO a R) = 4%nat /\ lb_big (blocks_MEMBIO a R) = 0.
Proof.
  intros a R. unfold blocks_MEMBIO, MEMBIO_BYTES. rewrite !lb_bytes_cons, !lb_big_cons. cbn [blk_size snd length lb_bytes lb_big fold_right].
  unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. rewrite !big1_small by (unfold BIGB; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma img_memflag : Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) memflag_foot.
Proof. unfold memflag_foot, A_mem_inited, IMG_LO, IMG_HI. apply Forall_cons; [cbn; lia| apply Forall_nil]. Qed.
Lemma img_CTX_X : Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) CTX_X.
Proof.
  unfold CTX_X, A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_in_init_config_key, A_load_strings_once, A_optsdone_lock,
    A_td_cancelbuf, A_keys, A_next_key, A_key_lock, IMG_LO, IMG_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma img_ERR_X : Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) ERR_X.
Proof.
  unfold ERR_X, A_err_string_once, A_defctx_inited, A_tevent_once, A_load_strings_once, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main, IMG_LO, IMG_HI. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma img_VDSO_X : Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) VDSO_X.
Proof. unfold VDSO_X, A_vdso_func, IMG_LO, IMG_HI. apply Forall_cons; [cbn; lia| apply Forall_nil]. Qed.
Lemma img_foot_nmb : forall ph, Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) (memflag_foot ++ ctxph_foot ph).
Proof. intros ph. apply Forall_app. split; [apply img_memflag| apply Forall_ctxph_foot; apply img_CTX_X]. Qed.
Lemma avoid_of_img : forall X A n, Forall (fun iv : Z * Z => IMG_LO <= fst iv /\ snd iv <= IMG_HI) X ->
  (A + n <= IMG_LO \/ IMG_HI <= A) -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.
Proof. intros X A n FX HA. eapply Forall_impl; [| exact FX]. intros [lo hi] K. cbn in K |- *. lia. Qed.

Section OBJ.
  Context {HCEIL : HeapCeil}.
  Lemma MEMBIO_mono : forall L L' m a R, MEMBIO L m a R -> (forall b, In b L -> In b L') -> MEMBIO L' m a R.
  Proof.
    intros L L' m a R MB SUB. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & REST).
    repeat match goal with |- _ /\ _ => split end; try assumption; try (apply SUB; assumption); apply REST.
  Qed.
  Lemma MEMBIO_frame0 : forall L L' SP m m' a R,
    MEMBIO L m a R -> (forall b, In b (blocks_MEMBIO a R) -> In b L') -> xpres L' SP [] m m' -> MEMBIO L' m' a R.
  Proof.
    intros L L' SP m m' a R MB KEEP XP. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & REST).
    assert (K1 : In (mb_id R, a, BIO_SIZE) L') by (apply KEEP; left; reflexivity).
    assert (K2 : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L') by (apply KEEP; right; left; reflexivity).
    assert (K3 : In (mb_bmid R, mb_bm R, BUFMEM_SIZE) L') by (apply KEEP; right; right; left; reflexivity).
    assert (K4 : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L') by (apply KEEP; right; right; right; left; reflexivity).
    repeat match goal with |- _ /\ _ => split end; try assumption; try apply REST.
    - eapply xpres_rw_cells'; [exact XP| exact C1| | apply Forall_nil]. right; right. exists (mb_id R, a, BIO_SIZE). split; [exact K1|].
      unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C2| | apply Forall_nil]. right; right. exists (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE). split; [exact K2|].
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIOBUFMEM_SIZE. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C3| | apply Forall_nil]. right; right. exists (mb_bmid R, mb_bm R, BUFMEM_SIZE). split; [exact K3|].
      unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BUFMEM_SIZE. lia.
    - eapply xpres_rw_cells'; [exact XP| exact C4| | apply Forall_nil]. right; right. exists (mb_rpid R, mb_rp R, BUFMEM_SIZE). split; [exact K4|].
      unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BUFMEM_SIZE. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma STOREobj_empty : forall L m A p,
    STOREobj L m A (store_empty p) <-> (rw_cells rsegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ In (p, A, STORE_SIZE) L).
  Proof. intros L m A p. unfold STOREobj, store_empty, ENTRIES. cbn [es_entries es_entries_o es_id]. intuition. Qed.
End OBJ.

Lemma perm7 : forall (E4 NB LE MB LA LB : list block) (sb : block),
  Permutation (E4 ++ NB ++ LE ++ MB ++ LA ++ sb :: LB) ((sb :: NB) ++ (E4 ++ LE ++ MB ++ LA ++ LB)).
Proof.
  intros. symmetry. cbn [app]. change (sb :: NB ++ E4 ++ LE ++ MB ++ LA ++ LB) with (sb :: (NB ++ E4 ++ LE ++ MB ++ LA ++ LB)).
  transitivity ((E4 ++ NB ++ LE ++ MB ++ LA) ++ sb :: LB); [| rewrite !app_assoc; apply Permutation_refl].
  apply Permutation_cons_app. transitivity (E4 ++ NB ++ LE ++ MB ++ LA ++ LB); [apply Permutation_app_swap_app| rewrite !app_assoc; apply Permutation_refl].
Qed.
Lemma perm5 : forall (E4 LE MB LA LB : list block), Permutation (E4 ++ LE ++ MB ++ LA ++ LB) (MB ++ (E4 ++ LE ++ LA ++ LB)).
Proof.
  intros. transitivity ((E4 ++ LE) ++ MB ++ (LA ++ LB)); [rewrite !app_assoc; apply Permutation_refl|].
  transitivity (MB ++ (E4 ++ LE) ++ (LA ++ LB)); [apply Permutation_app_swap_app| rewrite !app_assoc; apply Permutation_refl].
Qed.

Lemma errph_foot_below {HCEIL : HeapCeil} : forall LIB m cph eph (hi : Z),
  ERRPH_mid LIB m cph eph -> (forall b, In b LIB -> blk_addr b + blk_size b <= hi) -> Forall (fun iv : Z * Z => snd iv <= hi) (errph_foot eph).
Proof.
  intros LIB m [|x] [|c] hi P HB; cbn [ERRPH_mid ERRPH errph_foot] in *; try apply Forall_nil; [destruct P|].
  destruct P as [_ CH]. destruct CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
  apply Forall_cons; [| apply Forall_nil]. cbn. pose proof (HB _ I5) as K. rewrite Z5 in K. exact K.
Qed.

Section HHW.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma client_outside_block : forall s L m b LB SP q,
    hs_RHEAP H s L m -> In b L -> (forall b', In b' LB -> In b' L) -> idsdisj [b] LB -> hceil <= SP ->
    rclient_addr LB SP q -> q + 1 <= blk_addr b \/ blk_addr b + blk_size b <= q.
  Proof.
    intros s L m b LB SP q HP Hb SUB D CE HC. hcb.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5).
    destruct HC as [K|[[K NS]|(b' & Hb' & Hr)]]; [lia| lia|].
    pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ b b' HP Hb (SUB _ Hb') (D b b' ltac:(left; reflexivity) Hb')). lia.
  Qed.

End HHW.
