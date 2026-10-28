(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit
     ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C7 ECH_AStmt_C13 ECH_AStmt_C14.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_ids_app_ne_s : forall (l1 l2 : list block) b1 b2,
  List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ _ ND' H1 H2)].
  intros E. apply NI. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact H2.
Qed.
Definition idsdisj (X Y : list block) : Prop := forall b b', In b X -> In b' Y -> blk_id b <> blk_id b'.
Lemma nd_app : forall X Y, List.NoDup (map blk_id (X ++ Y)) -> idsdisj X Y /\ List.NoDup (map blk_id Y).
Proof.
  intros X Y ND. split; [intros b b' Hb Hb'; eapply nodup_ids_app_ne_s; eassumption|].
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
Lemma perm_in_rest_s : forall (Fr L' L : list block) b, Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b P HI NF. apply Permutation_sym in P. pose proof (Permutation_in _ P HI) as K. apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.
Lemma lb_bytes_app_s : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !lb_bytes_cons, IH. lia. Qed.
Lemma lb_bytes_perm_s : forall L L', Permutation L L' -> lb_bytes L = lb_bytes L'.
Proof.
  intros L L' P. induction P; [reflexivity| rewrite !lb_bytes_cons; lia| rewrite !lb_bytes_cons; lia| lia].
Qed.
Lemma lb_bytes_nonneg_s : forall L, Forall (fun b => 0 <= blk_size b) L -> 0 <= lb_bytes L.
Proof. induction L as [|b L IH]; intros F; [apply Z.le_refl|]. rewrite lb_bytes_cons. pose proof (Forall_inv F) as K. cbn beta in K. pose proof (IH (Forall_inv_tail F)) as K'. lia. Qed.

(* [comment removed for export] *)
Lemma errph_nonneg : forall eph, 0 <= errph_bytes eph /\ 0 <= errph_cnt eph.
Proof. intros [|c]; cbn [errph_bytes errph_cnt]; unfold ERRINIT_BYTES, ERRINIT_CNT; lia. Qed.
Lemma readcfg_stack_lo : forall M, 9152 <= READCFG_STACK M.
Proof. intros M. unfold READCFG_STACK, FR_OSSL_ECHSTORE_read_echconfiglist, FR_ech_read_priv_echconfiglist, AREALLOC_STACK, AFS_STACK. lia. Qed.
Lemma readcfg_stack_ready : forall M f' x E' v',
  READCFG_STACK (mkMID f' (CtxReady x) (mid_err M) E' v') <= READCFG_STACK M.
Proof.
  intros [f [|b] eph E v] f' x E' v'; unfold READCFG_STACK, mid_stack; cbn [mid_ctx mid_err ctxph_stack]; [| lia].
  unfold GETDEFCTX_STACK, CTXINIT_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context, AREALLOC_STACK, AFS_STACK. lia.
Qed.
Lemma membio_blocks_facts : forall a R,
  lb_bytes (blocks_MEMBIO a R) = MEMBIO_BYTES /\ length (blocks_MEMBIO a R) = 4%nat.
Proof.
  intros a R. unfold blocks_MEMBIO, MEMBIO_BYTES. rewrite !lb_bytes_cons. cbn [blk_size snd length lb_bytes fold_right].
  unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. lia.
Qed.

(* [comment removed for export] *)
Definition in_aimg (iv : Z * Z) : Prop := 0 <= fst iv /\ snd iv <= AIMG_TOP.
Lemma aimg_memflag : Forall in_aimg memflag_foot.
Proof. unfold memflag_foot, A_mem_inited, in_aimg, AIMG_TOP. apply Forall_cons; [cbn; lia| apply Forall_nil]. Qed.
Lemma aimg_CTX_X : Forall in_aimg CTX_X.
Proof.
  unfold CTX_X, in_aimg, AIMG_TOP. unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once,
    A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_base_once, A_base_ret,
    A_optsdone, A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf,
    A_keys, A_next_key, A_key_lock, A_tsd_main, LIBKEY0.
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma aimg_ERR_X : Forall in_aimg ERR_X.
Proof.
  unfold ERR_X, in_aimg, AIMG_TOP. unfold A_err_string_once, A_err_string_ret, A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
    A_defctx_inited, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_base_once, A_base_ret, A_optsdone, A_optsdone_lock, A_init_lock,
    A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main, LIBKEY0.
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma aimg_ERR_XE : Forall in_aimg ERR_XE.
Proof.
  unfold ERR_XE. apply Forall_app. split; [| apply aimg_ERR_X]. unfold ERRNO_X, ARERRNO, ATP, in_aimg, AIMG_TOP.
  repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma aimg_VDSO_X : Forall in_aimg VDSO_X.
Proof. unfold VDSO_X, A_vdso_func, in_aimg, AIMG_TOP. apply Forall_cons; [cbn; lia| apply Forall_nil]. Qed.
Lemma aimg_ctxph_foot : forall ph, Forall in_aimg (ctxph_foot ph).
Proof.
  intros ph. apply Forall_ctxph_foot. apply Forall_app. split; [apply aimg_CTX_X|].
  unfold AERRNO_X, ATP, in_aimg, AIMG_TOP. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma aimg_foot_nmb : forall ph, Forall in_aimg (memflag_foot ++ ctxph_foot ph).
Proof. intros ph. apply Forall_app. split; [apply aimg_memflag| apply aimg_ctxph_foot]. Qed.
Lemma avoid_of_aimg : forall X A n, Forall in_aimg X -> AIMG_TOP <= A -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.
Proof. intros X A n FX HA. eapply Forall_impl; [| exact FX]. intros [lo hi] K. unfold in_aimg in K. cbn in K |- *. lia. Qed.
(* [comment removed for export] *)
Lemma avoid_of_aimg_sh : forall X A n, Forall in_aimg X -> AIMG_TOP <= A -> Forall (fun iv : Z * Z => sh A + n <= fst iv \/ snd iv <= sh A) X.
Proof.
  intros X A n FX HA. eapply Forall_impl; [| exact FX]. intros [lo hi] K. unfold in_aimg in K. cbn in K |- *. right.
  unfold sh. rewrite ASHADOW_BASE_val. unfold AIMG_TOP in *. pose proof (Z.div_pos A 8). lia.
Qed.
(* [comment removed for export] *)
Lemma stack0_ok_of_aimg {HCEIL : HeapCeil} : forall X, Forall in_aimg X -> Forall stack0_ok X.
Proof.
  intros X FX. eapply Forall_impl; [| exact FX]. intros [lo hi] K. unfold in_aimg in K. cbn in K. unfold stack0_ok. cbn. right.
  pose proof aceil_range. unfold sh. rewrite ASHADOW_BASE_val. unfold AIMG_TOP in K. Z.div_mod_to_equations. lia.
Qed.

Section OBJ.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Lemma MEMBIO_mono : forall L L' m a R, MEMBIO H L m a R -> (forall b, In b L -> In b L') -> MEMBIO H L' m a R.
  Proof.
    intros L L' m a R MB SUB. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & REST).
    repeat match goal with |- _ /\ _ => split end; try assumption; try (apply SUB; assumption); apply REST.
  Qed.
  Lemma MEMBIO_frame0 : forall L L' SP m m' a R,
    MEMBIO H L m a R -> (forall b, In b (blocks_MEMBIO a R) -> In b L') -> xpres H L' SP [] m m' -> MEMBIO H L' m' a R.
  Proof.
    intros L L' SP m m' a R MB KEEP XP. unfold MEMBIO in *.
    destruct MB as (C1 & C2 & C3 & C4 & I1 & I2 & I3 & I4 & REST).
    assert (K1 : In (mb_id R, a, BIO_SIZE) L') by (apply KEEP; left; reflexivity).
    assert (K2 : In (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE) L') by (apply KEEP; right; left; reflexivity).
    assert (K3 : In (mb_bmid R, mb_bm R, BUFMEM_SIZE) L') by (apply KEEP; right; right; left; reflexivity).
    assert (K4 : In (mb_rpid R, mb_rp R, BUFMEM_SIZE) L') by (apply KEEP; right; right; right; left; reflexivity).
    repeat match goal with |- _ /\ _ => split end; try assumption; try apply REST.
    - eapply xpres_rw_cells; [exact XP| exact C1|]. split; [| apply Forall_nil]. right; right; left. exists (mb_id R, a, BIO_SIZE). split; [exact K1|].
      unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply xpres_rw_cells; [exact XP| exact C2|]. split; [| apply Forall_nil]. right; right; left. exists (mb_bbid R, mb_bb R, BIOBUFMEM_SIZE). split; [exact K2|].
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIOBUFMEM_SIZE. lia.
    - eapply xpres_rw_cells; [exact XP| exact C3|]. split; [| apply Forall_nil]. right; right; left. exists (mb_bmid R, mb_bm R, BUFMEM_SIZE). split; [exact K3|].
      unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BUFMEM_SIZE. lia.
    - eapply xpres_rw_cells; [exact XP| exact C4|]. split; [| apply Forall_nil]. right; right; left. exists (mb_rpid R, mb_rp R, BUFMEM_SIZE). split; [exact K4|].
      unfold buf_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BUFMEM_SIZE. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma STOREobj_empty : forall L m A p,
    STOREobj L m A (store_empty p) <-> (rw_cells asegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ In (p, A, STORE_SIZE) L).
  Proof. intros L m A p. unfold STOREobj, store_empty, ENTRIES. cbn [es_entries es_entries_o es_id]. intuition. Qed.
  Lemma STORE_shad_empty : forall m A p, STORE_shad m A (store_empty p) <-> (A + STORE_SIZE <= AAPP_HI /\ addressable m A STORE_SIZE).
  Proof. intros m A p. unfold STORE_shad, store_empty, ENTRIES_shad. cbn [es_entries es_entries_o]. intuition. Qed.

  (* [comment removed for export] *)
  Lemma blk_addressable_xpres : forall LB SP X m m' b A n,
    xpres H LB SP X m m' -> In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= blk_addr b -> (blk_addr b) mod 8 = 0 ->
    A mod 8 = 0 -> 0 <= n ->
    Forall (fun iv : Z * Z => sh A + nsh n <= fst iv \/ snd iv <= sh A) X ->
    addressable m A n -> addressable m' A n.
  Proof.
    intros LB SP X m m' b A n XP Hb B1 B2 B0 B8 A8 N0 FX (Hn & A0 & A8' & [UB UW]).
    assert (CL : xclient_range H LB SP X (sh A) (nsh n)).
    { split; [| exact FX]. right; right; right; left. exists b. split; [exact Hb|].
      unfold sh, nsh. pose proof (Z.div_le_mono (blk_addr b) A 8 ltac:(lia) B1).
      assert (A + n + 7 <= blk_addr b + blk_size b + 7) by lia.
      pose proof (Z.div_le_mono (A + n + 7 - A) (blk_addr b + blk_size b + 7 - blk_addr b) 8 ltac:(lia)).
      Z.div_mod_to_equations. nia. }
    split; [exact Hn|]. split; [exact A0|]. split; [exact A8'|].
    rewrite <- (shadow_of_length n) in CL by lia. split.
    - eapply xpres_bytes_at; [exact XP| exact UB| exact CL].
    - eapply xpres_wr_at; [exact XP| exact UW| exact CL].
  Qed.
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
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma client_outside_block : forall s L m b LB SP q,
    as_RHEAP H s L m -> In b L -> (forall b', In b' LB -> In b' L) -> idsdisj [b] LB -> aceil <= SP ->
    aclient_addr H LB SP q -> q + 1 <= blk_addr b \/ blk_addr b + blk_size b <= q.
  Proof.
    intros s L m b LB SP q HP Hb SUB D CE HC. acb.
    pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (ah_fsb H HH _ _ _ HP) as (F1 & F2 & F3 & F4).
    assert (SH0 : forall x, 0 <= x -> ASHADOW_BASE <= sh x) by (intros x Hx; unfold sh; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
    unfold aclient_addr, aimg_client, in_block, in_block_sh in HC. unfold aapp, aapp_lo, aapp_hi in B7.
    destruct HC as [K|[K|[(b' & Hb' & Hr)|[(b' & Hb' & Hr)|[K|[K|K]]]]]].
    - lia.
    - unfold AIMG_TOP, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
    - pose proof (ah_disj H HH _ _ _ _ _ HP Hb (SUB _ Hb') (D b b' ltac:(left; reflexivity) Hb')). lia.
    - pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb')) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). pose proof (SH0 (blk_addr b') ltac:(lia)).
      rewrite ASHADOW_BASE_val in *. unfold AIMG_TOP, AHI_LO, ALOWSH_LO in *. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - lia.
    - pose proof (SH0 (as_FSB H) ltac:(unfold AIMG_TOP in F1; lia)).
      assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_app (as_FSB H + AFS_SIZE) QB) as SB.
      rewrite ASHADOW_BASE_val in *. unfold AIMG_TOP, AHI_LO, ALOWSH_LO in *. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - assert (QA : 0 <= aceil) by lia. pose proof (SH0 aceil QA). rewrite ASHADOW_BASE_val in *. unfold AIMG_TOP, AHI_LO, ALOWSH_LO in *.
      destruct B7 as [[P1 P2]|[P1 P2]]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_drop_nonclient : forall LB SP X Y m m',
    xpres H LB SP (X ++ Y) m m' -> (forall q, rin_ivs Y q -> aclient_addr H LB SP q -> False) -> xpres H LB SP X m m'.
  Proof.
    intros LB SP X Y m m' XP HY q Hq [HC HX]. apply XP; [exact Hq|]. split; [exact HC|].
    intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (HX K)| exact (HY _ K HC)].
  Qed.
End HHW.
