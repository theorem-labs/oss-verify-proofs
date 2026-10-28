(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_ALibMF ECH_ALibOK ECH_Iface ECH_AKit
     ECH_AStmt_C1 ECH_AStmt_C2 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C11 ECH_AStmt_C14.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac unfold_addrs_in Ha :=
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold LIBKEY0, A_malloc_impl, A_realloc_impl, A_free_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_err_string_ret,
    A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
    A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
    A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_global_cleanup, A_base_once, A_base_ret, A_optsdone,
    A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in Ha;
  cbn in Ha.
Local Ltac solve_in_LIBX_mv :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold_addrs_in Ha;
  split; [| unfold A_mem_inited, A_vdso_func; split; lia];
  left;
  lazymatch type of Ha with
  | ?lo <= a < ?hi => apply (sub_iv_b_sound lo hi LIBX a); [vm_compute; reflexivity | exact Ha]
  end.
Local Ltac frame_conj AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX_mv]
        | eapply none_on_agree_mv; [exact AG | eassumption | solve_in_LIBX_mv | | ];
          unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
            A_defctx_exmeth_bio, A_tevent_once, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret, A_load_strings_once, A_load_strings_ret,
            A_optsdone_lock, A_init_lock, A_optsdone, A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main, A_err_string_lock, A_int_error_hash, A_err_string_once,
            A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_ret, A_glob_tevent_reg, LIBKEY0; lia
        | assumption ].
Local Ltac frame_group AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj AG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ERR_statics_frame_mv : forall LIB m m' c, ERR_statics m c -> magree (lib_addr_mv LIB) m m' -> ERR_statics m' c.
Proof. intros LIB m m' c S AG. unfold ERR_statics in *. frame_group AG. Qed.
Lemma ERR_fresh_core_frame_mv : forall LIB m m', ERR_fresh_core m -> magree (lib_addr_mv LIB) m m' -> ERR_fresh_core m'.
Proof. intros LIB m m' S AG. unfold ERR_fresh_core in *. frame_group AG. Qed.
Lemma ERR_fresh_frame_mv : forall LIB m m', ERR_fresh m -> magree (lib_addr_mv LIB) m m' -> ERR_fresh m'.
Proof. intros LIB m m' [C K] AG. split; [eapply ERR_fresh_core_frame_mv; eauto| eapply CTX_keys_frame_mv; eauto]. Qed.
Lemma ERR_chain_frame_mv : forall LIB m m' c, ERR_chain LIB m c -> magree (lib_addr_mv LIB) m m' -> ERR_chain LIB m' c.
Proof.
  intros LIB m m' c CH AG. unfold ERR_chain in *.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  assert (BR : forall b a, In b LIB -> In b (chain_blocks c) -> blk_addr b <= a < blk_addr b + blk_size b -> lib_addr_mv LIB a).
  { intros b a Hb Hc Ha. pose proof (proj1 (Forall_forall _ _) RR b Hc) as AR. unfold arange in AR. acb.
    split; [right; left; exists b; split; [exact Hb| exact Ha]|]. unfold A_mem_inited, A_vdso_func, AIMG_TOP in *. split; lia. }
  unfold chain_blocks in BR. unfold O_MKEY_ERR in *.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply rw_cells_agree; [exact AG| exact K2|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    eapply (BR (ec_mkey c)); [exact I2| cbn; tauto| lia].
  - eapply rw_cells_agree; [exact AG| exact K3|]. intros a Ha. unfold in_range, sa_cells in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    eapply (BR (ec_sa c)); [exact I3| cbn; tauto| lia].
  - eapply rw_cells_agree; [exact AG| exact K4|]. intros a Ha. unfold in_range in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    eapply (BR (ec_nodes c)); [exact I4| cbn; tauto| lia].
Qed.
Lemma ERRPH_frame_mv : forall LIB m m' ph, ERRPH LIB m ph -> magree (lib_addr_mv LIB) m m' -> ERRPH LIB m' ph.
Proof.
  intros LIB m m' [|c] P AG; cbn [ERRPH] in *.
  - eapply ERR_fresh_frame_mv; eauto.
  - destruct P as [S C]. split; [eapply ERR_statics_frame_mv; eauto| eapply ERR_chain_frame_mv; eauto].
Qed.

(* [comment removed for export] *)
Lemma addressable_agreeR : forall (R : Z -> Prop) m m' A n,
  magree R m m' -> (forall a, sh A <= a < sh A + nsh n -> R a) -> addressable m A n -> addressable m' A n.
Proof.
  intros R m m' A n AG HR (Hn & A0 & A8 & B & W). pose proof (shadow_of_length n Hn) as SL.
  split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
  - eapply bytes_at_agree; [exact AG| exact B|]. intros a Ha. apply HR. unfold in_range in *. lia.
  - eapply wr_at_agree; [exact AG| exact W|]. intros a Ha. apply HR. unfold in_range in *. lia.
Qed.
Lemma lib_shad_agreeR : forall (R : Z -> Prop) L m m',
  magree R m m' -> (forall a, in_block_sh L a -> R a) -> lib_shad L m -> lib_shad L m'.
Proof.
  intros R L m m' AG HR SH. unfold lib_shad in *. apply Forall_forall. intros b Hb.
  eapply addressable_agreeR; [exact AG| | exact (proj1 (Forall_forall _ _) SH b Hb)].
  intros a Ha. apply HR. exists b. split; [exact Hb| exact Ha].
Qed.
(* [comment removed for export] *)
Lemma ERRXR_agreeR : forall (R : Z -> Prop) m m' c E,
  magree R m m' -> (forall a, in_range (blk_addr (ec_es c)) ERRST_SIZE a -> R a) -> (forall a, in_block_sh (blocks_ERRST E) a -> R a) ->
  (forall a, in_block (blocks_ERRST E) a -> R a) ->
  ERRXR m c E -> ERRXR m' c E.
Proof.
  intros R m m' c E AG H1 H2 H3 (ES & OK & SH & SC). split; [eapply ERRST_agree; [exact AG| exact ES| exact H1]|].
  split; [exact OK|]. split; [eapply lib_shad_agreeR; [exact AG| exact H2| exact SH]|].
  unfold estrs_cells in *. apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) SC _ Hb) as [bs BC]. exists bs.
  eapply rw_cells_agree; [exact AG| exact BC|]. intros a Ha. apply H3. exists b. split; [exact Hb|].
  unfold in_range in Ha. revert Ha. cbn [cells_size csize]. rewrite Nat.add_0_r. intros Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ERR_chain_relist : forall L L' m c, ERR_chain L m c -> Forall (fun b => In b L') (chain_blocks c) -> ERR_chain L' m c.
Proof.
  intros L L' m c CH HF. unfold ERR_chain, chain_blocks in *.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  pose proof (Forall_inv HF) as J2. pose proof (Forall_inv (Forall_inv_tail HF)) as J3.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as J4.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF)))) as J5.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF))))) as J6.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
Lemma ERR_chain_mono : forall L L' m c, ERR_chain L m c -> (forall b, In b L -> In b L') -> ERR_chain L' m c.
Proof.
  intros L L' m c CH SUB. eapply ERR_chain_relist; [exact CH|]. unfold chain_blocks.
  destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  repeat (apply Forall_cons; [apply SUB; assumption|]). apply Forall_nil.
Qed.
Lemma ERRPH_mono : forall L L' m eph, ERRPH L m eph -> (forall b, In b L -> In b L') -> ERRPH L' m eph.
Proof. intros L L' m [|c] P SUB; cbn [ERRPH] in *; [exact P|]. destruct P as [ES CH]. split; [exact ES| eapply ERR_chain_mono; eassumption]. Qed.
Lemma ERRPH_mid_mono : forall L L' m cph eph, ERRPH_mid L m cph eph -> (forall b, In b L -> In b L') -> ERRPH_mid L' m cph eph.
Proof.
  intros L L' m [|x] [|c] P SUB; cbn [ERRPH_mid ERRPH] in *; try exact P.
  destruct P as [ES CH]. split; [exact ES| eapply ERR_chain_mono; eassumption].
Qed.
Lemma LIBMID_mono : forall L L' m M, LIBMID L m M -> (forall b, In b L -> In b L') -> LIBMID L' m M.
Proof.
  intros L L' m M LM SUB. destruct LM as (IM & MF & CP & EP & EX & REST).
  split; [exact IM|]. split; [exact MF|]. split; [eapply CTXPH_mono; eassumption|]. split; [eapply ERRPH_mid_mono; eassumption|].
  split; [exact EX| exact REST].
Qed.
Lemma ERRPH_mid_chain : forall LIB m cph c, ERRPH_mid LIB m cph (ErrReady c) -> ERR_chain LIB m c.
Proof. intros LIB m [|x] c P; cbn [ERRPH_mid ERRPH] in P; [destruct P| exact (proj2 P)]. Qed.
Lemma CTXPH_recontent : forall L L' m m' x, CTXPH L m (CtxReady x) -> CTXPH L' m' (CtxReady x) -> CTXPH L m' (CtxReady x).
Proof.
  intros L L' m m' x [_ [[I1 [Z1 [R1 _]]] EXO]] [CS' [[_ [_ [_ MU']]] _]]. cbn [CTXPH].
  split; [exact CS'|]. split; [exact (conj I1 (conj Z1 (conj R1 MU')))| exact EXO].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mid_newlib_ok_trans : forall M0 M1 M2 L1 L2,
  mid_step M0 M1 -> mid_newlib_ok M0 M1 L1 -> mid_step M1 M2 -> mid_newlib_ok M1 M2 L2 -> mid_newlib_ok M0 M2 (L2 ++ L1).
Proof.
  intros [f0 c0 e0 E0 v0] [f1 c1 e1 E1 v1] [f2 c2 e2 E2 v2] L1 L2 S1 N1 S2 N2.
  unfold mid_step, mid_newlib_ok in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *.
  destruct S1 as (_ & SC1 & SE1 & _). destruct S2 as (_ & SC2 & SE2 & _).
  destruct N1 as (LA1 & LE1 & P1 & C1 & R1). destruct N2 as (LA2 & LE2 & P2 & C2 & R2).
  exists (LA2 ++ LA1), (LE2 ++ LE1). split.
  { transitivity ((LA2 ++ LE2) ++ (LA1 ++ LE1)); [apply Permutation_app; assumption|].
    rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  split.
  - destruct c1 as [|b1].
    + destruct c0 as [|b0]; [| discriminate (SC1 b0 eq_refl)]. cbn in C1. subst LA1. rewrite app_nil_r. exact C2.
    + subst LA2. cbn [app]. rewrite (SC2 b1 eq_refl). destruct c0 as [|b0]; [exact C1|].
      cbn [ctxph_delta] in C1. destruct C1 as [_ ->]. reflexivity.
  - destruct e1 as [|d1].
    + destruct e0 as [|d0]; [| discriminate (SE1 d0 eq_refl)]. cbn in R1. subst LE1. rewrite app_nil_r. exact R2.
    + subst LE2. cbn [app]. rewrite (SE2 d1 eq_refl). destruct e0 as [|d0]; [exact R1|].
      cbn [errph_delta] in R1. destruct R1 as [_ ->]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blocks_ERRST_zero : blocks_ERRST errst_zero = [].
Proof. reflexivity. Qed.
Lemma errst_fits_zero : errst_fits errst_zero.
Proof. unfold errst_fits, errst_zero. cbn [es_slots]. repeat (apply Forall_cons; [cbn; unfold ERRDEBUG_BYTES; lia|]). apply Forall_nil. Qed.
Lemma Forall_firstn_es : forall (P : errslot -> Prop) ss i, Forall P ss -> Forall P (firstn i ss).
Proof. intros P ss i F. revert i. induction F as [|y ss Py F IH]; intros [|i]; cbn; try constructor; auto. Qed.
Lemma Forall_skipn_es : forall (P : errslot -> Prop) ss j, Forall P ss -> Forall P (skipn j ss).
Proof. intros P ss j F. revert j. induction F as [|y ss Py F IH]; intros [|j]; cbn; try constructor; auto. Qed.
Lemma Forall_slot_upd : forall (P : errslot -> Prop) ss i x, Forall P ss -> P x -> Forall P (slot_upd ss i x).
Proof. intros P ss i x F Px. unfold slot_upd. apply Forall_app. split; [apply Forall_firstn_es; exact F| apply Forall_cons; [exact Px| apply Forall_skipn_es; exact F]]. Qed.
Lemma Forall_slot_at : forall (P : errslot -> Prop) E i, Forall P (es_slots E) -> P (slot_clear 0) -> P (slot_at E i).
Proof.
  intros P E i F P0. unfold slot_at. destruct (nth_error (es_slots E) (Z.to_nat i)) as [s|] eqn:N.
  - rewrite (nth_error_nth _ _ _ N). exact (proj1 (Forall_forall _ _) F s (nth_error_In _ _ N)).
  - rewrite nth_overflow; [exact P0|]. apply nth_error_None. exact N.
Qed.
Lemma errst_fits_raise : forall E A1 p1 n1 line A2 p2 n2 lib reason,
  errst_fits E -> raise_sizes A1 n1 A2 n2 -> errst_fits (errst_raise E A1 p1 n1 line A2 p2 n2 lib reason).
Proof.
  intros E A1 p1 n1 line A2 p2 n2 lib reason FE (_ & P1 & _ & P2). unfold errst_raise, errst_seterr, errst_debug, errst_new, errst_fits.
  cbn [es_slots es_top es_bottom].
  set (E1 := mkERRST (slot_upd (es_slots E) (Z.to_nat (err_next (es_top E))) (slot_clear (2 ^ 32 - 1))) (err_next (es_top E))
                     (if err_next (es_top E) =? es_bottom E then err_next (es_bottom E) else es_bottom E)).
  assert (F1 : errst_fits E1).
  { unfold errst_fits, E1. cbn [es_slots]. apply Forall_slot_upd; [exact FE|]. cbn. unfold ERRDEBUG_BYTES. lia. }
  set (x2 := mkSLOT (sl_flags (slot_at E1 (err_next (es_top E)))) (sl_buffer (slot_at E1 (err_next (es_top E)))) A1 (Some (p1, n1)) line A2 (Some (p2, n2))).
  assert (P2x : lb_bytes (blocks_slot x2) <= ERRDEBUG_BYTES).
  { unfold x2. cbn [blocks_slot sl_file sl_file_o sl_func sl_func_o blocks_of app lb_bytes fold_right blk_size snd fst]. unfold ERRDEBUG_BYTES. lia. }
  set (E2 := mkERRST (slot_upd (es_slots E1) (Z.to_nat (es_top E1)) x2) (es_top E1) (es_bottom E1)).
  assert (F2 : errst_fits E2).
  { unfold errst_fits, E2. cbn [es_slots]. apply Forall_slot_upd; [exact F1| exact P2x]. }
  change (Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES)
            (slot_upd (es_slots E2) (Z.to_nat (es_top E2))
               (mkSLOT (sl_flags (slot_at E2 (es_top E2))) (ERR_PACK lib reason) (sl_file (slot_at E2 (es_top E2))) (sl_file_o (slot_at E2 (es_top E2)))
                       (sl_line (slot_at E2 (es_top E2))) (sl_func (slot_at E2 (es_top E2))) (sl_func_o (slot_at E2 (es_top E2)))))).
  apply Forall_slot_upd; [exact F2|].
  pose proof (Forall_slot_at _ E2 (es_top E2) F2 ltac:(cbn; unfold ERRDEBUG_BYTES; lia)) as Q.
  cbn [blocks_slot sl_file sl_file_o sl_func sl_func_o] in Q |- *. exact Q.
Qed.
Lemma lb_bytes_app : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. intros L1 L2. unfold lb_bytes. induction L1 as [|b L1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.
Lemma errst_fits_bounds : forall E, length (es_slots E) = 16%nat -> errst_fits E ->
  Z.of_nat (length (blocks_ERRST E)) <= ERRSTR_CNT /\ lb_bytes (blocks_ERRST E) <= ERRSTR_BYTES.
Proof.
  intros E LEN FE. unfold blocks_ERRST, ERRSTR_CNT, ERRSTR_BYTES. unfold errst_fits in FE.
  assert (GEN : forall ss, Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES) ss ->
            Z.of_nat (length (concat (map blocks_slot ss))) <= 2 * Z.of_nat (length ss)
            /\ lb_bytes (concat (map blocks_slot ss)) <= ERRDEBUG_BYTES * Z.of_nat (length ss)).
  { intros ss F. induction F as [|y ss PB F IH]; [cbn; lia|]. cbn [map concat length].
    rewrite length_app, lb_bytes_app.
    assert (L2 : (length (blocks_slot y) <= 2)%nat).
    { unfold blocks_slot. rewrite length_app. destruct (sl_file_o y) as [[? ?]|]; destruct (sl_func_o y) as [[? ?]|]; cbn; lia. }
    destruct IH as [IH1 IH2]. unfold ERRDEBUG_BYTES in *. lia. }
  destruct (GEN _ FE) as [G1 G2]. rewrite LEN in G1, G2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G1, G2. unfold ERRDEBUG_BYTES in G2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition xR (LBx : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop := aclient_addr H LBx SP a /\ ~ rin_ivs X a.
  Lemma magree_of_xpres : forall LBx SP X m m', xpres H LBx SP X m m' -> magree (xR LBx SP X) m m'.
  Proof. intros LBx SP X m m' XP a Ha [HC HX]. exact (XP a Ha (conj HC HX)). Qed.

  Lemma chain_blocks_in : forall LIB m c b, ERR_chain LIB m c -> In b (chain_blocks c) -> In b LIB.
  Proof.
    intros LIB m c b CH Hb. destruct CH as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
    unfold chain_blocks in Hb. cbn in Hb. destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_xagree : forall LIB LBx SP X m m' M x f' (v' : bool),
    LIBMID LIB m M -> mid_ctx M = CtxReady x ->
    xpres H LBx SP X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> rin_ivs LIBX a -> (A_mem_inited <= a < A_mem_inited + 1) \/ (A_vdso_func <= a < A_vdso_func + 8)) ->
    (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' f' -> rw_cells asegs m' A_vdso_func [C8 (wz (if v' then 0 else P_cgt_init))] ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID f' (mid_ctx M) (mid_err M) (mid_E M) v').
  Proof.
    intros until v'. intros LM CX XP SUBL SUBE XS XR XB XBS XES MF' VD' XEB.
    destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & SH & BL).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG.
    assert (AGmv : magree (lib_addr_mv LIB) m m').
    { eapply magree_mono; [exact AG|]. intros a (HL & NF & NV). split.
      - destruct HL as [HX|[HB|HBS]].
        + right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia.
        + right; right; left. destruct HB as (b & Hb & R). exists b. split; [apply SUBL; exact Hb| exact R].
        + right; right; right; left. destruct HBS as (b & Hb & R). exists b. split; [apply SUBL; exact Hb| exact R].
      - intros K. destruct HL as [HX|[HB|HBS]]; [destruct (XS a K HX); tauto| exact (XB a K HB)| exact (XBS a K HBS)]. }
    assert (AGrel : forall A cs (P : Prop), rw_cells asegs m A cs -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 -> rw_cells asegs m' A cs).
    { intros A cs _ RC B1 B2. eapply rw_cells_agree; [exact AG| exact RC|]. intros a Ha. unfold in_range in Ha.
      split; [right; left; unfold aimg_client; lia| intros K; exact (XR a K ltac:(lia))]. }
    unfold mid_errblocks in *. remember (mid_err M) as eph eqn:EE. rewrite CX in CP, EPm.
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso]. rewrite CX.
    split. { unfold IMPL_mem in *. frame_group AGmv. }
    split; [exact MF'|].
    split. { eapply CTXPH_frame_mv; [exact CP| exact AGmv]. }
    split. { cbn [ERRPH_mid] in *. eapply ERRPH_frame_mv; [exact EPm| exact AGmv]. }
    split. { destruct eph as [|c]; cbn [ERRX] in *; [exact EX|].
             pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH. pose proof CH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
             eapply ERRXR_agreeR; [exact AG| | | | exact EX].
             - intros a Ha. unfold in_range in Ha. assert (HB : in_block LIB a) by (exists (ec_es c); split; [exact I5| rewrite Z5; lia]).
               split; [right; right; left; destruct HB as (b & Hb & R); exists b; split; [apply SUBL; exact Hb| exact R]| intros K; exact (XB a K HB)].
             - intros a Ha. split; [| intros K; exact (XES a K Ha)].
               right; right; right; left. destruct Ha as (b & Hb & R). exists b. split; [apply SUBE; exact Hb| exact R].
             - intros a Ha. split; [| intros K; exact (XEB a K Ha)].
               right; right; left. destruct Ha as (b & Hb & R). exists b. split; [apply SUBE; exact Hb| exact R]. }
    split; [exact VD'|].
    split. { eapply none_agree; [exact AGmv| unfold A_global_cleanup; lia| | exact CL].
             split; [| unfold A_global_cleanup, A_mem_inited, A_vdso_func; split; lia].
             left. apply (sub_iv_b_sound A_global_cleanup (A_global_cleanup + 1) LIBX A_global_cleanup); [vm_compute; reflexivity| lia]. }
    split; [exact FIT|].
    split. { unfold GOT_mem in *. eapply (AGrel _ _ True); [exact G1| unfold A_got_CRYPTO_malloc; lia| unfold A_got_CRYPTO_malloc; cbn; lia]. }
    split. { unfold GOT_echfree in *. eapply (AGrel _ _ True); [exact G2| unfold A_got_ossl_echext_free; lia| unfold A_got_ossl_echext_free; cbn; lia]. }
    split. { unfold GOT_x509vpm in *. eapply (AGrel _ _ True); [exact G3| unfold A_got_ASN1_OBJECT_free; lia| unfold A_got_ASN1_OBJECT_free; cbn; lia]. }
    split. { unfold METH_mem in *. eapply (AGrel _ _ True); [exact M1| unfold A_mem_buf_method, O_METH_BREAD; lia| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold METH_b64 in *. eapply (AGrel _ _ True); [exact M2| unfold A_b64_method, O_METH_BREAD; lia| unfold A_b64_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW in *.
             repeat match goal with K : _ /\ _ |- _ => destruct K end.
             repeat match goal with |- _ /\ _ => split end; try exact I;
               (eapply (AGrel _ _ True); [eassumption| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; lia| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; cbn; lia]). }
    split. { unfold relro_lib, arelro_lib in *. intros i Hi.
             destruct (AG i ltac:(lia) ltac:(split; [right; left; unfold aimg_client; lia| intros K; exact (XR i K ltac:(lia))])) as [E _].
             rewrite E. apply RL. exact Hi. }
    split. { destruct eph as [|c]; cbn [errph_shad] in *; [exact I|].
             pose proof (ERRPH_mid_chain _ _ _ _ EPm) as CH.
             eapply lib_shad_agreeR; [exact AG| | exact SH]. intros a (b & Hb & R).
             assert (HBS : in_block_sh LIB a) by (exists b; split; [eapply chain_blocks_in; [exact CH| exact Hb]| exact R]).
             split; [| intros K; exact (XBS a K HBS)].
             right; right; right; left. destruct HBS as (b' & Hb' & R'). exists b'. split; [apply SUBL; exact Hb'| exact R']. }
    exact BL.
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_xpres0 : forall LIB LBx SP m m' M x,
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP [] m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> LIBMID LIB m' M.
  Proof.
    intros LIB LBx SP m m' M x LM CX XP SUBL SUBE. pose proof LM as (_ & MF & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG.
    assert (R1 : forall a, rin_ivs LIBX a -> xR LBx SP [] a).
    { intros a HX. split; [| intros K; exact K]. right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia. }
    pose proof (LIBMID_xagree LIB LBx SP [] m m' M x (mid_flag M) (mid_vdso M) LM CX XP SUBL SUBE
                  ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K)) as K.
    destruct M as [f c e E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. apply K.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_mem_inited (A_mem_inited + 1) LIBX a); [vm_compute; reflexivity| unfold A_mem_inited; lia].
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K0; destruct K0.
  Qed.

  Hypothesis HH : asan_rt_hyps H.
  (* [comment removed for export] *)
  Lemma in_block_where : forall s LBx m0 L a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> in_block L a -> AIMG_TOP <= a < aceil.
  Proof.
    intros s LBx m0 L a HP SUB (b & Hb & R). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & _ & D4 & D5 & _). lia.
  Qed.
  Lemma in_block_sh_where : forall s LBx m0 L a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> in_block_sh L a -> sh AIMG_TOP <= a < sh aceil.
  Proof.
    intros s LBx m0 L a HP SUB (b & Hb & R). pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (_ & _ & D3 & _ & _ & _ & D7).
    pose proof (sh_aapp_range _ _ D7 D3) as (S1 & S2 & S3). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_mfX : forall s m0 LIB LBx SP X m m' M x,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP (memflag_foot ++ X) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> ~ rin_ivs LIBX a) -> (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' 1 ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP X m m' M x HP LM CX XP SUBL SUBE X1 X2 X3 X4 X5 MF' X6. pose proof LM as (_ & _ & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG. acb.
    assert (MFL : forall a, rin_ivs memflag_foot a -> A_mem_inited <= a < A_mem_inited + 1) by (intros a Ha; unfold memflag_foot in Ha; cbn in Ha; lia).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    eapply LIBMID_xagree; [exact LM| exact CX| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'| |].
    - intros a K HX. apply rin_ivs_app in K. destruct K as [K|K]; [left; exact (MFL a K)| destruct (X1 a K HX)].
    - intros a K R. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia| exact (X2 a K R)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X3 a K HB)].
      pose proof (in_block_where _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X4 a K HB)].
      pose proof (in_block_sh_where _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X5 a K HB)].
      pose proof (in_block_sh_where _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. unfold_addrs_in Ha. split.
      + right; left. unfold aimg_client. lia.
      + intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia|].
        apply (X1 a K). apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X6 a K HB)].
      pose proof (in_block_where _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_mf : forall s m0 LIB LBx SP m m' M x,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP memflag_foot m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> MEMFLAG m' 1 ->
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP m m' M x HP LM CX XP SUBL SUBE MF'.
    apply (LIBMID_mfX s m0 LIB LBx SP [] m m' M x HP LM CX).
    - eapply xpres_X_mono; [exact XP|]. intros a K. apply rin_ivs_app. left. exact K.
    - exact SUBL.
    - exact SUBE.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - intros a K; destruct K.
    - exact MF'.
    - intros a K; destruct K.
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_vdso : forall s m0 LIB LBx SP m m' M x,
    as_RHEAP H s LBx m0 ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP VDSO_X m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    rw_cells asegs m' A_vdso_func [C8 (wz 0)] ->
    LIBMID LIB m' (mkMID (mid_flag M) (mid_ctx M) (mid_err M) (mid_E M) true).
  Proof.
    intros s m0 LIB LBx SP m m' M x HP LM CX XP SUBL SUBE VD'. pose proof LM as (_ & MF & _).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG. acb.
    assert (VFL : forall a, rin_ivs VDSO_X a -> A_vdso_func <= a < A_vdso_func + 8) by (intros a Ha; unfold VDSO_X in Ha; cbn in Ha; lia).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    eapply (LIBMID_xagree LIB LBx SP VDSO_X m m' M x (mid_flag M) true); [exact LM| exact CX| exact XP| exact SUBL| exact SUBE| | | | | | | exact VD'|].
    - intros a K HX. right. exact (VFL a K).
    - intros a K R. pose proof (VFL a K). unfold A_vdso_func in *. lia.
    - intros a K HB. pose proof (in_block_where _ _ _ _ _ HP SUBL HB). pose proof (VFL a K). unfold A_vdso_func, AIMG_TOP in *. lia.
    - intros a K HB. pose proof (in_block_sh_where _ _ _ _ _ HP SUBL HB). pose proof (VFL a K). unfold A_vdso_func, AIMG_TOP in *. lia.
    - intros a K HB. pose proof (in_block_sh_where _ _ _ _ _ HP SUBE HB). pose proof (VFL a K). unfold A_vdso_func, AIMG_TOP in *. lia.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. unfold_addrs_in Ha. split.
      + right; left. unfold aimg_client. lia.
      + intros K. pose proof (VFL a K). unfold A_vdso_func in *. lia.
    - intros a K HB. pose proof (in_block_where _ _ _ _ _ HP SUBE HB). pose proof (VFL a K). unfold A_vdso_func, AIMG_TOP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_scratch_lo : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> AIMG_TOP <= fst iv.
  Proof.
    intros LF m iv R SC. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4).
    destruct SC as [->|(k & ff & fp & FF & E)]; cbn [fst]; [lia|].
    pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity. unfold AFS_HDR, AFS_FLAGS in *.
    destruct E as [-> |[-> | ->]]; cbn [fst]; [lia| lia|]. unfold sh in *. unfold AIMG_TOP in *. rewrite ?ASHADOW_BASE_val in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fs_scratch_off_block : forall s LBx m0 L LF m iv a,
    as_RHEAP H s LBx m0 -> (forall b, In b L -> In b LBx) -> as_RFS H LF m -> fs_scratch H LF iv ->
    fst iv <= a < snd iv -> ~ in_block L a /\ ~ in_block_sh L a.
  Proof.
    intros s LBx m0 L LF m iv a HP SUB R SC Ha. split; intros (b & Hb & Rb).
    - destruct b as [[p A] n]. cbn [blk_addr blk_size fst snd] in Rb.
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
      pose proof (fsobj_scratch H HH LF A n m iv R (fsobj_block H HH _ _ _ LF _ _ _ HP (SUB _ Hb)) ltac:(lia) ltac:(lia)
                    ltac:(pose proof (aapp_bounds _ _ B7 ltac:(lia)); lia) B7 SC). lia.
    - destruct b as [[p A] n]. cbn [blk_addr blk_size fst snd] in Rb.
      pose proof (ah_blocks H HH _ _ _ _ HP (SUB _ Hb)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
      pose proof (fsobj_scratch_sh H HH LF A n m iv R (fsobj_block H HH _ _ _ LF _ _ _ HP (SUB _ Hb)) ltac:(lia) ltac:(lia)
                    ltac:(pose proof (aapp_bounds _ _ B7 ltac:(lia)); lia) SC). lia.
  Qed.
  Lemma rin_ivs_In : forall X a, rin_ivs X a -> exists iv, In iv X /\ fst iv <= a < snd iv.
  Proof. intros X a. induction X as [|iv X IH]; cbn; intros K; [destruct K|]. destruct K as [K|K]; [exists iv; auto| destruct (IH K) as (iv' & I & R); exists iv'; auto]. Qed.


  (* [comment removed for export] *)
  Lemma LIBMID_xsX : forall s m0 LIB LBx SP XS LF X m m' M x f' (v' : bool),
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP (XS ++ X) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> rin_ivs LIBX a -> (A_mem_inited <= a < A_mem_inited + 1) \/ (A_vdso_func <= a < A_vdso_func + 8)) ->
    (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' f' -> rw_cells asegs m' A_vdso_func [C8 (wz (if v' then 0 else P_cgt_init))] ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID f' (mid_ctx M) (mid_err M) (mid_E M) v').
  Proof.
    intros until v'. intros HP RF SCR LM CX XP SUBL SUBE X1 X2 X3 X4 X5 MF' VD' X6. acb.
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    assert (XSoff : forall L a, (forall b, In b L -> In b LBx) -> rin_ivs XS a -> ~ in_block L a /\ ~ in_block_sh L a).
    { intros L a SUB K. destruct (rin_ivs_In _ _ K) as (iv & I & R).
      eapply fs_scratch_off_block; [exact HP| exact SUB| exact RF| exact (proj1 (Forall_forall _ _) SCR iv I)| exact R]. }
    eapply LIBMID_xagree; [exact LM| exact CX| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'| exact VD'|].
    - intros a K HX. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X1 a K HX)]. pose proof (XSlo a K). pose proof (LIBX_below a HX). lia.
    - intros a K R. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (XSlo a K); unfold AIMG_TOP in *; lia| exact (X2 a K R)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [exact (proj1 (XSoff LIB a SUBL K) HB)| exact (X3 a K HB)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [exact (proj2 (XSoff LIB a SUBL K) HB)| exact (X4 a K HB)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [exact (proj2 (XSoff _ a SUBE K) HB)| exact (X5 a K HB)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [exact (proj1 (XSoff _ a SUBE K) HB)| exact (X6 a K HB)].
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_xs : forall s m0 LIB LBx SP XS LF m m' M x,
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP XS m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) -> LIBMID LIB m' M.
  Proof.
    intros s m0 LIB LBx SP XS LF m m' M x HP RF SCR LM CX XP SUBL SUBE. pose proof LM as (_ & MF & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG. acb.
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    assert (R1 : forall a, rin_ivs LIBX a -> xR LBx SP XS a).
    { intros a HX. pose proof (LIBX_below a HX). split; [| intros K; pose proof (XSlo a K); lia].
      right; left. pose proof (alo_libx_proof a HX) as W. unfold alibx_ok, aimg_client in *. lia. }
    assert (XP' : xpres H LBx SP (XS ++ []) m m') by (rewrite app_nil_r; exact XP).
    pose proof (LIBMID_xsX s m0 LIB LBx SP XS LF [] m m' M x (mid_flag M) (mid_vdso M) HP RF SCR LM CX XP' SUBL SUBE
                  ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K) ltac:(intros a K; destruct K)) as K.
    destruct M as [f c e E v]; cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. apply K.
    - destruct MF as (fb & MF1 & MF2). exists fb. split; [| exact MF2].
      eapply rw_cells_agree; [exact AG| exact MF1|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_mem_inited (A_mem_inited + 1) LIBX a); [vm_compute; reflexivity| unfold A_mem_inited; lia].
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. apply R1. unfold_addrs_in Ha.
      apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K0; destruct K0.
  Qed.
  (* [comment removed for export] *)
  Lemma LIBMID_xs_mfX : forall s m0 LIB LBx SP XS LF X m m' M x,
    as_RHEAP H s LBx m0 -> as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x -> xpres H LBx SP (XS ++ memflag_foot ++ X) m m' ->
    (forall b, In b LIB -> In b LBx) -> (forall b, In b (mid_errblocks M) -> In b LBx) ->
    (forall a, rin_ivs X a -> ~ rin_ivs LIBX a) -> (forall a, rin_ivs X a -> ~ (0x571000 <= a < 0x5ea000)) ->
    (forall a, rin_ivs X a -> ~ in_block LIB a) -> (forall a, rin_ivs X a -> ~ in_block_sh LIB a) ->
    (forall a, rin_ivs X a -> ~ in_block_sh (mid_errblocks M) a) ->
    MEMFLAG m' 1 ->
    (forall a, rin_ivs X a -> ~ in_block (mid_errblocks M) a) ->          (* [comment removed for export] *)
    LIBMID LIB m' (mkMID 1 (mid_ctx M) (mid_err M) (mid_E M) (mid_vdso M)).
  Proof.
    intros s m0 LIB LBx SP XS LF X m m' M x HP RF SCR LM CX XP SUBL SUBE X1 X2 X3 X4 X5 MF' X6. pose proof LM as (_ & _ & _ & _ & _ & VD & _).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG. acb. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    assert (MFL : forall a, rin_ivs memflag_foot a -> A_mem_inited <= a < A_mem_inited + 1) by (intros a Ha; unfold memflag_foot in Ha; cbn in Ha; lia).
    eapply (LIBMID_xsX s m0 LIB LBx SP XS LF (memflag_foot ++ X)); [exact HP| exact RF| exact SCR| exact LM| exact CX| exact XP| exact SUBL| exact SUBE| | | | | | exact MF'| |].
    - intros a K HX. apply rin_ivs_app in K. destruct K as [K|K]; [left; exact (MFL a K)| destruct (X1 a K HX)].
    - intros a K R. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia| exact (X2 a K R)].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X3 a K HB)].
      pose proof (in_block_where _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X4 a K HB)].
      pose proof (in_block_sh_where _ _ _ _ _ HP SUBL HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X5 a K HB)].
      pose proof (in_block_sh_where _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
    - eapply rw_cells_agree; [exact AG| exact VD|]. intros a Ha. unfold_addrs_in Ha. split.
      + right; left. unfold aimg_client. lia.
      + intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (XSlo a K); unfold AIMG_TOP in *; lia|].
        apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFL a K); unfold A_mem_inited in *; lia|].
        apply (X1 a K). apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| unfold A_vdso_func; lia].
    - intros a K HB. apply rin_ivs_app in K. destruct K as [K|K]; [| exact (X6 a K HB)].
      pose proof (in_block_where _ _ _ _ _ HP SUBE HB). pose proof (MFL a K). unfold A_mem_inited, AIMG_TOP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma LIBMID_errcall : forall s m0 s' LIB LB SP XS LF LBN m m' M x c E',
    as_RHEAP H s (mid_errblocks M ++ LB) m0 -> (forall b, In b LIB -> In b LB) ->
    LIBMID LIB m M -> mid_ctx M = CtxReady x ->
    as_RFS H LF m -> Forall (fs_scratch H LF) XS ->
    xpres H LB SP (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M)) m m' ->          (* [comment removed for export] *)
    as_RHEAP H s' (blocks_ERRST E' ++ LBN ++ LB) m' ->
    CTXPH (LBN ++ LB) m' (CtxReady x) -> ERRPH (LBN ++ LB) m' (ErrReady c) -> errph_delta (mid_err M) LBN c ->
    ERRXR m' c E' -> errst_fits E' -> lib_shad (chain_blocks c) m' -> MEMFLAG m' 1 ->
    LIBMID (LBN ++ LIB) m' (mkMID 1 (CtxReady x) (ErrReady c) E' (mid_vdso M)).
  Proof.
    intros until E'. intros HP SUBL LM CX RF SCR XP HP' CP' EP' D EX' FIT' SHC MF'.
    destruct LM as (IM & MF & CP & EPm & EX & VD & CL & FIT & G1 & G2 & G3 & M1 & M2 & HT & RL & SH & BL).
    pose proof (magree_of_xpres _ _ _ _ _ XP) as AG. acb. assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
    rewrite CX in CP, EPm. cbn [ERRPH_mid] in EPm.
    (* [comment removed for export] *)
    assert (XSlo : forall a, rin_ivs XS a -> AIMG_TOP <= a).
    { intros a K. destruct (rin_ivs_In _ _ K) as (iv & I & R). pose proof (fs_scratch_lo LF m iv RF (proj1 (Forall_forall _ _) SCR iv I)). lia. }
    assert (EFlo : forall a, rin_ivs (errph_foot (mid_err M)) a -> AIMG_TOP <= a).
    { intros a K. destruct (mid_err M) as [|c0]; cbn [errph_foot rin_ivs fst snd] in K; [destruct K|]. destruct K as [K|[]].
      pose proof (ERRPH_mid_chain LIB m (CtxReady x) c0 EPm) as CH0.
      pose proof CH0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
      pose proof (in_block_where _ _ _ _ a HP ltac:(intros b Hb; apply in_or_app; right; apply SUBL; exact Hb)
                    ltac:(exists (ec_es c0); split; [exact I5| rewrite Z5; exact K])). lia. }
    assert (ERRXlo : forall a, rin_ivs ERR_XE a -> a < AIMG_TOP /\ ~ (A_malloc_impl <= a < A_free_impl + 8) /\ ~ (A_vdso_func <= a < A_vdso_func + 8) /\ ~ (A_global_cleanup <= a < A_global_cleanup + 1) /\ ~ (0x571000 <= a < 0x5ea000)).
    { intros a K. unfold ERR_XE, ERRNO_X, ARERRNO in K. unfold ATP in K. cbn [app] in K. unfold ERR_X in K. cbn [rin_ivs fst snd] in K.
      unfold LIBKEY0, A_err_string_once, A_err_string_ret, A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
        A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
        A_key_lock, A_tsd_main, A_malloc_impl, A_free_impl, A_vdso_func, A_global_cleanup, AIMG_TOP in *. cbn in K.
      repeat (destruct K as [K|K]); lia. }
    assert (MFlo : forall a, rin_ivs memflag_foot a -> A_mem_inited <= a < A_mem_inited + 1) by (intros a Ha; unfold memflag_foot in Ha; cbn in Ha; lia).
    (* [comment removed for export] *)
    assert (STAT : forall A (k : nat), (forall a, A <= a < A + Z.of_nat k -> rin_ivs LIBX a) ->
              (A + Z.of_nat k <= A_mem_inited \/ A_mem_inited + 1 <= A) -> (forall a, A <= a < A + Z.of_nat k -> ~ rin_ivs ERR_XE a) ->
              forall a, in_range A (Z.of_nat k) a -> xR LB SP (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M)) a).
    { intros A k HX HF HE a Ha. unfold in_range in Ha.
      assert (R : A <= a < A + Z.of_nat k) by lia. pose proof (HX a R) as LX. pose proof (alo_libx_proof a LX) as W.
      assert (LO : a < AIMG_TOP) by (apply LIBX_below; exact LX).
      split; [right; left; unfold alibx_ok, aimg_client in *; lia|].
      intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (XSlo a K); lia|].
      apply rin_ivs_app in K. destruct K as [K|K]; [exact (HE a R K)|].
      apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFlo a K); lia| pose proof (EFlo a K); lia]. }
    assert (REL : forall A cs, rw_cells asegs m A cs -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0x5ea000 -> rw_cells asegs m' A cs).
    { intros A cs RC B1 B2. eapply rw_cells_agree; [exact AG| exact RC|]. intros a Ha. unfold in_range in Ha.
      split; [right; left; unfold aimg_client; lia|].
      intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (XSlo a K); unfold AIMG_TOP in *; lia|].
      apply rin_ivs_app in K. destruct K as [K|K]; [destruct (ERRXlo a K); lia|].
      apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFlo a K); unfold A_mem_inited in *; lia| pose proof (EFlo a K); unfold AIMG_TOP in *; lia]. }
    unfold LIBMID. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso ERRPH_mid ERRPH ERRX errph_shad errph_below].
    split. { (* [comment removed for export] *)
      destruct IM as (I1 & I2 & I3).
      split; [| split]; (eapply rw_cells_agree; [exact AG| eassumption|]); apply STAT; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
        first [ intros a Ha; first [ apply (sub_iv_b_sound A_malloc_impl (A_malloc_impl + 8) LIBX a); [vm_compute; reflexivity| exact Ha]
                                   | apply (sub_iv_b_sound A_realloc_impl (A_realloc_impl + 8) LIBX a); [vm_compute; reflexivity| exact Ha]
                                   | apply (sub_iv_b_sound A_free_impl (A_free_impl + 8) LIBX a); [vm_compute; reflexivity| exact Ha] ]
              | unfold A_malloc_impl, A_realloc_impl, A_free_impl, A_mem_inited; lia
              | intros a Ha K; destruct (ERRXlo a K); unfold A_malloc_impl, A_realloc_impl, A_free_impl in *; lia ]. }
    split; [exact MF'|].
    split; [apply (CTXPH_mono LIB (LBN ++ LIB) ltac:(intros b Hb; apply in_or_app; right; exact Hb)); eapply CTXPH_recontent; [exact CP| exact CP']|].
    split. { destruct EP' as [ES' CH']. split; [exact ES'|]. eapply ERR_chain_relist; [exact CH'|].
             destruct (mid_err M) as [|c0]; cbn [errph_delta] in D.
             - destruct D as (_ & _ & HF). eapply Forall_impl; [| exact HF]. intros b Hb. apply in_or_app. left. exact Hb.
             - destruct D as [-> ->]. cbn [app]. pose proof (ERRPH_mid_chain LIB m (CtxReady x) c0 EPm) as CH0.
               apply Forall_forall. intros b Hb. eapply chain_blocks_in; [exact CH0| exact Hb]. }
    split; [exact EX'|].
    split. { eapply rw_cells_agree; [exact AG| exact VD|]. apply STAT; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             - intros a Ha. apply (sub_iv_b_sound A_vdso_func (A_vdso_func + 8) LIBX a); [vm_compute; reflexivity| exact Ha].
             - unfold A_vdso_func, A_mem_inited. lia.
             - intros a Ha K. destruct (ERRXlo a K). lia. }
    split. { eapply none_agree; [exact AG| unfold A_global_cleanup; lia| | exact CL].
             apply (STAT A_global_cleanup 1%nat); [| unfold A_global_cleanup, A_mem_inited; cbn; lia| | unfold in_range; cbn; lia].
             - intros a Ha. apply (sub_iv_b_sound A_global_cleanup (A_global_cleanup + 1) LIBX a); [vm_compute; reflexivity| cbn in Ha; lia].
             - intros a Ha K. destruct (ERRXlo a K). cbn in Ha. lia. }
    split; [exact FIT'|].
    split. { unfold GOT_mem in *. eapply REL; [exact G1| unfold A_got_CRYPTO_malloc; lia| unfold A_got_CRYPTO_malloc; cbn; lia]. }
    split. { unfold GOT_echfree in *. eapply REL; [exact G2| unfold A_got_ossl_echext_free; lia| unfold A_got_ossl_echext_free; cbn; lia]. }
    split. { unfold GOT_x509vpm in *. eapply REL; [exact G3| unfold A_got_ASN1_OBJECT_free; lia| unfold A_got_ASN1_OBJECT_free; cbn; lia]. }
    split. { unfold METH_mem in *. eapply REL; [exact M1| unfold A_mem_buf_method, O_METH_BREAD; lia| unfold A_mem_buf_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold METH_b64 in *. eapply REL; [exact M2| unfold A_b64_method, O_METH_BREAD; lia| unfold A_b64_method, O_METH_BREAD; cbn; lia]. }
    split. { unfold HPKE_tabs, id_rows, HPKE_KEM_IDS, HPKE_KDF_IDS, HPKE_AEAD_IDS, HPKE_KEM_ROW, HPKE_KDF_ROW, HPKE_AEAD_ROW in *.
             repeat match goal with K : _ /\ _ |- _ => destruct K end.
             repeat match goal with |- _ /\ _ => split end; try exact I;
               (eapply REL; [eassumption| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; lia| unfold A_hpke_kem_tab, A_hpke_kdf_tab, A_hpke_aead_tab; cbn; lia]). }
    split. { unfold relro_lib, arelro_lib in *. intros i Hi.
             assert (Ri : xR LB SP (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M)) i).
             { split; [right; left; unfold aimg_client; lia|].
               intros K. apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (XSlo i K); unfold AIMG_TOP in *; lia|].
               apply rin_ivs_app in K. destruct K as [K|K]; [destruct (ERRXlo i K); lia|].
               apply rin_ivs_app in K. destruct K as [K|K]; [pose proof (MFlo i K); unfold A_mem_inited in *; lia| pose proof (EFlo i K); unfold AIMG_TOP in *; lia]. }
             destruct (AG i ltac:(lia) Ri) as [E _]. rewrite E. apply RL. exact Hi. }
    split; [exact SHC|].
    (* [comment removed for export] *)
    destruct EP' as [_ CH']. pose proof CH' as (I2 & Z2 & _ & I3 & Z3 & _ & I4 & Z4 & _ & I5 & Z5 & I6 & Z6 & _).
    assert (BND : forall b, In b (LBN ++ LB) -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP' ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & B5 & _). exact B5. }
    unfold chain_below. rewrite <- Z2, <- Z3, <- Z4, <- Z5.
    assert (POS : forall b, In b (LBN ++ LB) -> 0 <= blk_addr b).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP' ltac:(apply in_or_app; right; exact Hb)) as (B1 & _). lia. }
    repeat split; first [apply BND; assumption| apply POS; assumption].
  Qed.
End W.

End HCW.
