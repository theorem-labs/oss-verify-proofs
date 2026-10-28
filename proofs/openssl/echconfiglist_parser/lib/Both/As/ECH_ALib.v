(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import InitMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_Iface ECH_ATraces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition arange (A n : Z) : Prop := 0 < A /\ A mod 16 = 0 /\ 0 <= n /\ AIMG_TOP <= A /\ A + n < 2^64.

Section LIB.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition magree (R : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> R a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma magree_mono : forall (R R' : Z -> Prop) m m', magree R m m' -> (forall a, R' a -> R a) -> magree R' m m'.
Proof. intros R R' m m' H HR a Ha Hr. apply H; auto. Qed.
Lemma magree_refl : forall R m, magree R m m.
Proof. intros R m a _ _. auto. Qed.
Lemma magree_trans : forall R m1 m2 m3, magree R m1 m2 -> magree R m2 m3 -> magree R m1 m3.
Proof. intros R m1 m2 m3 H1 H2 a Ha Hr. destruct (H1 a Ha Hr) as [E1 W1]. destruct (H2 a Ha Hr) as [E2 W2]. split; [congruence| auto]. Qed.

Definition in_range (A n : Z) (a : Z) : Prop := A <= a < A + n.

Lemma bytes_at_agree : forall R m m' A bs,
  magree R m m' -> bytes_at asegs m A bs -> (forall a, in_range A (Z.of_nat (length bs)) a -> R a) -> bytes_at asegs m' A bs.
Proof.
  intros R m m' A bs AG (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (AG (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; unfold in_range; lia)) as [E _]. rewrite E. reflexivity.
Qed.
Lemma wr_at_agree : forall R m m' A n,
  magree R m m' -> wr_at asegs m A n -> (forall a, in_range A n a -> R a) -> wr_at asegs m' A n.
Proof.
  intros R m m' A n AG (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (AG (A + i) ltac:(lia) ltac:(apply HR; unfold in_range; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma rw_cells_agree : forall R m m' A cs,
  magree R m m' -> rw_cells asegs m A cs -> (forall a, in_range A (Z.of_nat (cells_size cs)) a -> R a) -> rw_cells asegs m' A cs.
Proof.
  intros R m m' A cs AG [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.
Lemma u64arr_agree : forall R m m' A ws,
  magree R m m' -> u64arr asegs m A ws -> (forall a, in_range A (8 * Z.of_nat (length ws)) a -> R a) -> u64arr asegs m' A ws.
Proof.
  intros R m m' A ws AG [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u64s_length. intros a Ha. apply HR. unfold in_range in *. lia.
  - eapply wr_at_agree; eauto.
Qed.
Lemma u32arr_agree : forall R m m' A ws,
  magree R m m' -> u32arr asegs m A ws -> (forall a, in_range A (4 * Z.of_nat (length ws)) a -> R a) -> u32arr asegs m' A ws.
Proof.
  intros R m m' A ws AG [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u32s_length. intros a Ha. apply HR. unfold in_range in *. lia.
  - eapply wr_at_agree; eauto.
Qed.
Lemma none_agree : forall R m m' a, magree R m m' -> 0 <= a < 2^64 -> R a -> m (wa a) = None -> m' (wa a) = None.
Proof. intros R m m' a AG Ha Hr E. destruct (AG a Ha Hr) as [E' _]. congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_mem (m : mem) : Prop :=
  rw_cells asegs m A_got_CRYPTO_malloc
    [C8 (wz P_CRYPTO_malloc); C8 (wz P_CRYPTO_aligned_alloc); C8 (wz P_CRYPTO_realloc); C8 (wz P_CRYPTO_free)].
Definition GOT_echfree (m : mem) : Prop :=
  rw_cells asegs m A_got_ossl_echext_free [C8 (wz P_ossl_echext_free); C8 (wz P_ossl_echstore_entry_free)].
Definition GOT_x509vpm (m : mem) : Prop := rw_cells asegs m A_got_ASN1_OBJECT_free [C8 (wz P_ASN1_OBJECT_free)].
(* [comment removed for export] *)
Definition IMPL_mem (m : mem) : Prop :=
     rw_cells asegs m A_malloc_impl [C8 (wz P_CRYPTO_malloc)]
  /\ rw_cells asegs m A_realloc_impl [C8 (wz P_CRYPTO_realloc)]
  /\ rw_cells asegs m A_free_impl [C8 (wz P_CRYPTO_free)].
(* [comment removed for export] *)
Definition relro_lib (m : mem) : Prop := arelro_lib m.

Definition none_on (m : mem) (A n : Z) : Prop := forall a, A <= a < A + n -> m (wa a) = None.

(* [comment removed for export] *)
Lemma none_on_rw_cells : forall m A bs,
  none_on m A (Z.of_nat (length bs)) -> rw_bytes_b asegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  rw_cells asegs m A [CB (length bs) bs].
Proof.
  intros m A bs HN HB HA HL. apply rw_cells_image0; [| exact HB | exact HA | exact HL].
  intros a Ha. specialize (HN (bv_unsigned a) Ha). unfold wa in HN. rewrite Z_to_bv_bv_unsigned in HN. exact HN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lib_pristine (m : mem) : Prop := forall a, rin_ivs LIBX0 a -> m (wa a) = None.

(* [comment removed for export] *)
Definition musl0 (m : mem) : Prop :=
     rw_cells asegs m A_keys [C8 (wz A_keys0_val)]
  /\ rw_cells asegs m A_next_key [C4 (wz 0)]
  /\ rw_cells asegs m A_key_lock [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m A_td_tsd_used [C1 (b8 1)].

(* [comment removed for export] *)
Definition CTX_X : list (Z * Z) :=
  [ (A_destructor_key, A_destructor_key + 8);
    (A_defctx_inited, A_defctx_inited + 1); (A_defctx, A_defctx + 328);
    (A_defctx_tlkey, A_defctx_tlkey + 4); (A_defctx_tlkey_once, A_defctx_tlkey_once + 4); (A_defctx_tlkey_ret, A_defctx_tlkey_ret + 4);
    (A_defctx_once, A_defctx_once + 4); (A_defctx_once_ret, A_defctx_once_ret + 4);
    (A_base_inited, A_base_inited + 1); (A_in_init_config_key, A_in_init_config_key + 4);
    (A_base_once, A_base_once + 4); (A_base_ret, A_base_ret + 4);
    (A_optsdone_lock, A_optsdone_lock + 8); (A_init_lock, A_init_lock + 8);
    (A_td_cancelbuf, A_td_cancelbuf + 8);                              (* [comment removed for export] *)
    (A_keys + 8, A_keys + 32); (A_next_key, A_key_lock + 8) ].         (* [comment removed for export] *)
Definition ERR_X : list (Z * Z) :=
  [ (A_err_string_lock, A_err_string_lock + 8); (A_int_error_hash, A_int_error_hash + 8);
    (A_err_string_once, A_err_string_once + 4); (A_err_string_ret, A_err_string_ret + 4);
    (A_master_once, A_master_once + 4); (A_master_key, A_master_key + 4); (A_master_once_ret, A_master_once_ret + 1);
    (A_tevent_once, A_tevent_once + 4); (A_tevent_ret, A_tevent_ret + 4); (A_glob_tevent_reg, A_glob_tevent_reg + 8);
    (A_load_strings_once, A_load_strings_once + 4); (A_load_strings_ret, A_load_strings_ret + 4); (A_optsdone, A_optsdone + 8);
    (A_td_tsd_used, A_td_tsd_used + 1); (A_td_cancelbuf, A_td_cancelbuf + 8);
    (A_keys + 32, A_keys + 40); (A_next_key, A_key_lock + 8);         (* [comment removed for export] *)
    (A_tsd_main + 16, A_tsd_main + 24); (A_tsd_main + 32, A_tsd_main + 40) ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CTX_fresh (m : mem) : Prop :=
     none_on m A_destructor_key 8
  /\ none_on m A_defctx_inited 1 /\ none_on m A_defctx 328
  /\ none_on m A_defctx_tlkey 4 /\ none_on m A_defctx_tlkey_once 4 /\ none_on m A_defctx_tlkey_ret 4
  /\ none_on m A_defctx_once 4 /\ none_on m A_defctx_once_ret 4
  /\ none_on m A_base_inited 1 /\ none_on m A_stopped 1 /\ none_on m A_in_init_config_key 4
  /\ none_on m A_base_once 4 /\ none_on m A_base_ret 4 /\ none_on m A_load_strings_once 4 /\ none_on m A_load_strings_ret 4
  /\ none_on m A_optsdone_lock 8 /\ none_on m A_init_lock 8 /\ none_on m A_optsdone 8
  /\ none_on m A_td_cancelbuf 8
  /\ none_on m (A_keys + 8) (0x400 - 8)                               (* [comment removed for export] *)
  /\ none_on m (A_tsd_main + 8) 8                                    (* [comment removed for export] *)
  /\ musl0 m.
(* [comment removed for export] *)
Record ctxinfo := mkCX { cx_exlock : block ; cx_olock : Z ; cx_ilock : Z }.
Definition CTX_statics (m : mem) (x : ctxinfo) : Prop :=
     rw_cells asegs m A_defctx_inited [C1 (b8 1)]                            (* [comment removed for export] *)
  /\ rw_cells asegs m A_defctx_tlkey [C4 (wz LIBKEY0)]                      (* [comment removed for export] *)
  /\ rw_cells asegs m A_defctx_tlkey_once [C4 (wz 2)] /\ rw_cells asegs m A_defctx_tlkey_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_defctx_once [C4 (wz 2)] /\ rw_cells asegs m A_defctx_once_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_defctx_exlock [C8 (wz (blk_addr (cx_exlock x)))]     (* [comment removed for export] *)
  /\ rw_cells asegs m A_defctx_exmeth_bio [C8 (wz 0)]                        (* [comment removed for export] *)
  /\ rw_cells asegs m (A_tsd_main + 8 * LIBKEY0) [C8 (wz 0)]                 (* [comment removed for export] *)
  /\ rw_cells asegs m A_destructor_key [C4 (wz (LIBKEY0 + 1)); C4 (wz (2^32 - 1))]   (* [comment removed for export] *)
  /\ rw_cells asegs m A_base_inited [C1 (b8 1)]
  /\ rw_cells asegs m A_stopped [C1 (b8 0)]                                  (* [comment removed for export] *)
  /\ rw_cells asegs m A_in_init_config_key [C4 (wz (LIBKEY0 + 2))]          (* [comment removed for export] *)
  /\ rw_cells asegs m A_base_once [C4 (wz 2)] /\ rw_cells asegs m A_base_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_optsdone_lock [C8 (wz (cx_olock x))] /\ rw_cells asegs m A_init_lock [C8 (wz (cx_ilock x))]
  /\ rw_cells asegs m (A_keys + 8 * LIBKEY0) [C8 (wz P_nodtor); C8 (wz P_init_thread_destructor); C8 (wz P_nodtor)]   (* [comment removed for export] *)
  /\ rw_cells asegs m A_keys [C8 (wz A_keys0_val)].                         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition EXLOCK (LIB : list block) (m : mem) (b : block) : Prop :=
  In b LIB /\ blk_size b = MUTEX_SIZE /\ arange (blk_addr b) MUTEX_SIZE /\ MUTEX m (blk_addr b) 0.
Definition CTX_blocks (LIB : list block) (m : mem) (x : ctxinfo) : Prop :=
  EXLOCK LIB m (cx_exlock x) /\ (exists po pi, In (po, cx_olock x, 40) LIB /\ In (pi, cx_ilock x, 40) LIB).
(* [comment removed for export] *)
Definition CTX_keys (m : mem) : Prop :=
     rw_cells asegs m A_next_key [C4 (wz (LIBKEY0 + 2))]
  /\ rw_cells asegs m A_key_lock [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells asegs m A_td_cancelbuf [C8 (wz 0)]
  /\ rw_cells asegs m A_td_tsd_used [C1 (b8 1)].
Inductive ctxphase : Type := CtxFresh | CtxReady (x : ctxinfo).
Definition CTXPH (LIB : list block) (m : mem) (ph : ctxphase) : Prop :=
  match ph with
  | CtxFresh => CTX_fresh m
  | CtxReady x => CTX_statics m x /\ CTX_blocks LIB m x
  end.

(* [comment removed for export] *)
Definition ERR_fresh_core (m : mem) : Prop :=
     none_on m A_err_string_lock 8 /\ none_on m A_int_error_hash 8 /\ none_on m A_err_string_once 4 /\ none_on m A_err_string_ret 4
  /\ none_on m A_master_once 4 /\ none_on m A_master_key 4 /\ none_on m A_master_once_ret 1
  /\ none_on m A_tevent_once 4 /\ none_on m A_tevent_ret 4 /\ none_on m A_glob_tevent_reg 8
  /\ none_on m A_load_strings_once 4 /\ none_on m A_load_strings_ret 4 /\ none_on m A_optsdone 8
  /\ none_on m (A_keys + 8 * (LIBKEY0 + 3)) 8                          (* [comment removed for export] *)
  /\ none_on m (A_tsd_main + 8 * (LIBKEY0 + 1)) 8 /\ none_on m (A_tsd_main + 8 * (LIBKEY0 + 3)) 8.   (* [comment removed for export] *)
Definition ERR_fresh (m : mem) : Prop := ERR_fresh_core m /\ CTX_keys m.
Record errchain := mkEC { ec_mkey : block ; ec_sa : block ; ec_nodes : block ; ec_es : block ; ec_hands : block ;
                         ec_eslock : Z ; ec_eshash : Z ; ec_tevreg : Z }.
Definition O_MKEY_ERR : Z := 24.
Definition sa_cells (nodes : Z) : list cell := [C4 (wz 1); C4 (wz 0); C8 (wz 0); C8 (wz 1); C8 (wz nodes)].
Definition ERR_statics (m : mem) (c : errchain) : Prop :=
     rw_cells asegs m A_master_once_ret [C1 (b8 1)]                          (* [comment removed for export] *)
  /\ rw_cells asegs m A_master_once [C4 (wz 2)] /\ rw_cells asegs m A_master_key [C4 (wz (LIBKEY0 + 3))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (A_tsd_main + 8 * (LIBKEY0 + 3)) [C8 (wz (blk_addr (ec_mkey c)))]   (* [comment removed for export] *)
  /\ rw_cells asegs m A_stopped [C1 (b8 0)]
  /\ rw_cells asegs m A_base_once [C4 (wz 2)] /\ rw_cells asegs m A_base_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_load_strings_once [C4 (wz 2)] /\ rw_cells asegs m A_load_strings_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_optsdone [C8 (wz 2)]                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells asegs m A_err_string_once [C4 (wz 2)] /\ rw_cells asegs m A_err_string_ret [C4 (wz 1)]
  /\ rw_cells asegs m A_err_string_lock [C8 (wz (ec_eslock c))] /\ rw_cells asegs m A_int_error_hash [C8 (wz (ec_eshash c))]
  /\ rw_cells asegs m A_tevent_once [C4 (wz 2)] /\ rw_cells asegs m A_tevent_ret [C4 (wz 1)] /\ rw_cells asegs m A_glob_tevent_reg [C8 (wz (ec_tevreg c))]
  /\ rw_cells asegs m (A_keys + 8 * (LIBKEY0 + 3)) [C8 (wz P_err_delete_thread_state)]   (* [comment removed for export] *)
  /\ rw_cells asegs m A_next_key [C4 (wz (LIBKEY0 + 3))]                    (* [comment removed for export] *)
  /\ rw_cells asegs m A_key_lock [C8 (wz 0); C8 (wz 0)] /\ rw_cells asegs m A_td_cancelbuf [C8 (wz 0)]
  /\ rw_cells asegs m A_td_tsd_used [C1 (b8 1)]
  /\ rw_cells asegs m A_keys [C8 (wz A_keys0_val)]
  /\ rw_cells asegs m (A_tsd_main + 8 * (LIBKEY0 + 1)) [C8 (wz (blk_addr (ec_hands c)))]. (* [comment removed for export] *)
Definition chain_blocks (c : errchain) : list block := [ec_mkey c; ec_sa c; ec_nodes c; ec_es c; ec_hands c].
Definition ERR_chain (LIB : list block) (m : mem) (c : errchain) : Prop :=
     In (ec_mkey c) LIB /\ blk_size (ec_mkey c) = 72
  /\ rw_cells asegs m (blk_addr (ec_mkey c) + O_MKEY_ERR) [C8 (wz (blk_addr (ec_sa c)))]
  /\ In (ec_sa c) LIB /\ blk_size (ec_sa c) = 32
  /\ rw_cells asegs m (blk_addr (ec_sa c)) (sa_cells (blk_addr (ec_nodes c)))
  /\ In (ec_nodes c) LIB /\ blk_size (ec_nodes c) = 128
  /\ rw_cells asegs m (blk_addr (ec_nodes c)) [C8 (wz (blk_addr (ec_es c)))]
  /\ In (ec_es c) LIB /\ blk_size (ec_es c) = ERRST_SIZE
  /\ In (ec_hands c) LIB /\ blk_size (ec_hands c) = 8
  /\ Forall (fun b => arange (blk_addr b) (blk_size b)) (chain_blocks c).
Inductive errphase : Type := ErrFresh | ErrReady (c : errchain).
Definition ERRPH (LIB : list block) (m : mem) (ph : errphase) : Prop :=
  match ph with
  | ErrFresh => ERR_fresh m
  | ErrReady c => ERR_statics m c /\ ERR_chain LIB m c
  end.

(* [comment removed for export] *)
Record lib_inited := mkLI {
  li_ctx : ctxinfo ;
  li_chain : errchain ;
  li_vdso_done : bool }.
Inductive libst : Type := Fresh | Inited (i : lib_inited).
Definition lib_fresh : libst := Fresh.
Definition is_fresh (st : libst) : bool := match st with Fresh => true | Inited _ => false end.

Definition lib_statics_inited (m : mem) (i : lib_inited) : Prop :=
     IMPL_mem m
  /\ rw_cells asegs m A_vdso_func [C8 (wz (if li_vdso_done i then 0 else P_cgt_init))]
  /\ rw_cells asegs m A_mem_inited [C1 (b8 1)]
  /\ CTX_statics m (li_ctx i)
  /\ ERR_statics m (li_chain i)
  /\ m (wa A_global_cleanup) = None.

(* [comment removed for export] *)
Definition lib_shad (LIB : list block) (m : mem) : Prop := Forall (fun b => addressable m (blk_addr b) (blk_size b)) LIB.
Definition lib_blocks_inited (LIB : list block) (m : mem) (i : lib_inited) : Prop :=
     CTX_blocks LIB m (li_ctx i)
  /\ ERR_chain LIB m (li_chain i)
  /\ (exists E, ERRST LIB m (blk_addr (ec_es (li_chain i))) E /\ errst_canonical E)
  /\ lib_shad (chain_blocks (li_chain i)) m.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lib_fits (LIB : list block) : Prop := Z.of_nat (length LIB) <= 1800 /\ lb_bytes LIB <= 2^17.
Definition LIBST (st : libst) (LIB : list block) (m : mem) : Prop :=
  match st with
  | Fresh => LIB = [] /\ lib_pristine m /\ musl0 m
  | Inited i => lib_statics_inited m i /\ lib_blocks_inited LIB m i /\ lib_fits LIB
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LIBST_fresh_intro : forall m, lib_pristine m -> musl0 m -> LIBST lib_fresh [] m.
Proof. intros m H M. split; [reflexivity| split; [exact H| exact M]]. Qed.

Lemma LIBST_nil : forall st LIB m, LIBST st LIB m -> is_fresh st = true -> LIB = [].
Proof. intros [|i] LIB m H E; [exact (proj1 H)| discriminate]. Qed.

(* [comment removed for export] *)
Definition lib_addr (LIB : list block) (a : Z) : Prop := rin_ivs LIBX a \/ in_block LIB a \/ in_block_sh LIB a.

Lemma LIBX0_sub_LIBX : forall a, rin_ivs LIBX0 a -> rin_ivs LIBX a.
Proof. intros a H. unfold LIBX. apply (proj2 (rin_ivs_app _ _ _)). left. exact H. Qed.

(* [comment removed for export] *)
Definition sub_iv_b (lo hi : Z) (X : list (Z * Z)) : bool := existsb (fun iv => (fst iv <=? lo) && (hi <=? snd iv)) X.
Lemma sub_iv_b_sound : forall lo hi X a, sub_iv_b lo hi X = true -> lo <= a < hi -> rin_ivs X a.
Proof.
  intros lo hi X a H Ha. unfold sub_iv_b in H. apply existsb_exists in H. destruct H as [[l h] [Hin Hb]]. cbn in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  revert Hin. induction X as [|iv X IH]; intros Hin; [destruct Hin|]. cbn. destruct Hin as [E|Hin]; [left; subst iv; cbn; lia| right; exact (IH Hin)].
Qed.
Local Ltac solve_in_LIBX :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; left;
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold LIBKEY0, A_malloc_impl, A_realloc_impl, A_free_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_err_string_ret,
    A_err_string_lock, A_int_error_hash, A_master_once_ret, A_master_once, A_master_key,
    A_defctx_inited, A_defctx, A_defctx_exlock, A_defctx_exmeth_bio, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
    A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_stopped, A_base_inited, A_global_cleanup, A_base_once, A_base_ret, A_optsdone,
    A_optsdone_lock, A_init_lock, A_in_init_config_key, A_load_strings_once, A_load_strings_ret, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in Ha;
  cbn in Ha;
  lazymatch type of Ha with
  | ?lo <= a < ?hi => apply (sub_iv_b_sound lo hi LIBX a); [vm_compute; reflexivity | exact Ha]
  end.

Local Ltac solve_in_block HIN HSZ :=
  intros a Ha; right; left; eexists; split; [exact HIN|]; unfold in_range in Ha; rewrite ?HSZ;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul blk_addr blk_size fst snd] in *;
  unfold ERRST_SIZE, MUTEX_SIZE, O_MKEY_ERR in *; lia.

Lemma none_on_agree : forall R m m' A n, magree R m m' -> none_on m A n -> (forall a, in_range A n a -> R a) -> 0 <= A -> A + n <= 2^64 -> none_on m' A n.
Proof.
  intros R m m' A n AG H HR HA HN a Ha. eapply none_agree; [exact AG | lia | apply HR; exact Ha | apply H; exact Ha].
Qed.
Local Ltac frame_conj AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX]
        | eapply none_on_agree; [exact AG | eassumption | solve_in_LIBX | | ];
          unfold A_defctx_exmeth_bio, A_tsd_main, A_stopped, A_key_lock, A_keys, LIBKEY0; lia
        | assumption ].
Local Ltac frame_group AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj AG.

Lemma musl0_frame : forall LIB m m', musl0 m -> magree (lib_addr LIB) m m' -> musl0 m'.
Proof. intros LIB m m' S AG. unfold musl0 in *. frame_group AG. Qed.
Lemma CTX_statics_frame : forall LIB m m' x, CTX_statics m x -> magree (lib_addr LIB) m m' -> CTX_statics m' x.
Proof. intros LIB m m' x S AG. unfold CTX_statics in *. frame_group AG. Qed.
Lemma ERR_statics_frame : forall LIB m m' c, ERR_statics m c -> magree (lib_addr LIB) m m' -> ERR_statics m' c.
Proof. intros LIB m m' c S AG. unfold ERR_statics in *. frame_group AG. Qed.
Lemma CTX_keys_frame : forall LIB m m', CTX_keys m -> magree (lib_addr LIB) m m' -> CTX_keys m'.
Proof. intros LIB m m' S AG. unfold CTX_keys in *. frame_group AG. Qed.

Lemma lib_statics_frame : forall LIB m m' i, lib_statics_inited m i -> magree (lib_addr LIB) m m' -> lib_statics_inited m' i.
Proof.
  intros LIB m m' i S AG. unfold lib_statics_inited, IMPL_mem in *.
  destruct S as ((S1 & S1b & S1c) & S3 & S4 & SC & SE & SG).
  repeat match goal with |- _ /\ _ => split end;
    try (eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX]).
  - eapply CTX_statics_frame; eauto.
  - eapply ERR_statics_frame; eauto.
  - eapply none_agree; [exact AG | | | exact SG]; unfold A_global_cleanup; [lia|].
    left. apply (proj1 (in_ivs_b_spec LIBX A_global_cleanup)). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma LIBST_cleanup_byte : forall st LIB m, LIBST st LIB m -> m (wa A_global_cleanup) = None.
Proof.
  intros [|i] LIB m HL; cbn [LIBST] in HL.
  - destruct HL as (_ & P & _). apply P. apply (proj1 (in_ivs_b_spec LIBX0 A_global_cleanup)). vm_compute. reflexivity.
  - destruct HL as [S _]. unfold lib_statics_inited in S.
    destruct S as (_ & _ & _ & _ & _ & SG). exact SG.
Qed.
Lemma A_global_cleanup_eq : A_global_cleanup = ACLEANUP.
Proof. reflexivity. Qed.

Lemma ERRST_agree : forall R LB m m' a E,
  magree R m m' -> ERRST LB m a E -> (forall x, in_range a ERRST_SIZE x -> R x) -> ERRST LB m' a E.
Proof.
  intros R LB m m' a E AG H HR. unfold ERRST in *.
  destruct H as (L & T & B & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & OWN).
  assert (L16 : forall (f : errslot -> word), length (map f (es_slots E)) = 16%nat) by (intros f; rewrite length_map; exact L).
  assert (Z16 : length zero16 = 16%nat) by reflexivity.
  unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, ERRST_SIZE in *.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try first [ eapply u32arr_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; rewrite ?L16, ?Z16 in Hx; lia]
          | eapply u64arr_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; rewrite ?L16, ?Z16 in Hx; lia]
          | eapply rw_cells_agree; [exact AG | eassumption | intros x Hx; apply HR; unfold in_range in *; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia] ].
  all: lia.
Qed.

Lemma EXLOCK_frame : forall LIB m m' b, EXLOCK LIB m b -> magree (lib_addr LIB) m m' -> EXLOCK LIB m' b.
Proof.
  intros LIB m m' b (I1 & Z1 & R1 & C1) AG. unfold EXLOCK, MUTEX in *. destruct b as [[p1 a1] n1]. cbn [blk_addr blk_size fst snd] in *.
  split; [exact I1|]. split; [exact Z1|]. split; [exact R1|]. eapply rw_cells_agree; [exact AG | exact C1 | solve_in_block I1 Z1].
Qed.
Lemma CTX_blocks_frame : forall LIB m m' x, CTX_blocks LIB m x -> magree (lib_addr LIB) m m' -> CTX_blocks LIB m' x.
Proof. intros LIB m m' x [E O] AG. split; [eapply EXLOCK_frame; eauto | exact O]. Qed.
Lemma CTX_fresh_frame : forall LIB m m', CTX_fresh m -> magree (lib_addr LIB) m m' -> CTX_fresh m'.
Proof.
  intros LIB m m' S AG. unfold CTX_fresh in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end;
  first [ eapply musl0_frame; eassumption
        | (eapply none_on_agree; [exact AG | eassumption | solve_in_LIBX | | ]);
          unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
            A_tevent_once, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret, A_load_strings_once, A_load_strings_ret,
            A_optsdone_lock, A_init_lock, A_optsdone, A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main; lia ].
Qed.
Lemma CTXPH_frame : forall LIB m m' ph, CTXPH LIB m ph -> magree (lib_addr LIB) m m' -> CTXPH LIB m' ph.
Proof.
  intros LIB m m' [|x] C AG; cbn [CTXPH] in *.
  - eapply CTX_fresh_frame; eauto.
  - destruct C as [CS CB]. split; [eapply CTX_statics_frame; eauto| eapply CTX_blocks_frame; eauto].
Qed.

Lemma ERR_chain_frame : forall LIB m m' c, ERR_chain LIB m c -> magree (lib_addr LIB) m m' -> ERR_chain LIB m' c.
Proof.
  intros LIB m m' c B AG. unfold ERR_chain, sa_cells in *.
  destruct B as (I2 & Z2 & K2 & I3 & Z3 & K3 & I4 & Z4 & K4 & I5 & Z5 & I6 & Z6 & RR).
  destruct (ec_mkey c) as [[p2 a2] n2] eqn:E2. destruct (ec_sa c) as [[p3 a3] n3] eqn:E3.
  destruct (ec_nodes c) as [[p4 a4] n4] eqn:E4. destruct (ec_es c) as [[p5 a5] n5] eqn:E5. cbn [blk_addr blk_size fst snd] in *.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - eapply rw_cells_agree; [exact AG | exact K2 | solve_in_block I2 Z2].
  - eapply rw_cells_agree; [exact AG | exact K3 | solve_in_block I3 Z3].
  - eapply rw_cells_agree; [exact AG | exact K4 | solve_in_block I4 Z4].
Qed.
(* [comment removed for export] *)
Lemma ERR_fresh_frame : forall LIB m m', ERR_fresh m -> magree (lib_addr LIB) m m' -> ERR_fresh m'.
Proof.
  intros LIB m m' [C K] AG. split; [| eapply CTX_keys_frame; eauto]. unfold ERR_fresh_core in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end;
  (eapply none_on_agree; [exact AG | eassumption | solve_in_LIBX | | ]);
  unfold A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret,
    A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_keys, A_tsd_main, LIBKEY0; lia.
Qed.
Lemma ERRPH_frame : forall LIB m m' ph, ERRPH LIB m ph -> magree (lib_addr LIB) m m' -> ERRPH LIB m' ph.
Proof.
  intros LIB m m' [|c] E AG; cbn [ERRPH] in *.
  - eapply ERR_fresh_frame; eauto.
  - destruct E as [ES EC]. split; [eapply ERR_statics_frame; eauto| eapply ERR_chain_frame; eauto].
Qed.


(* [comment removed for export] *)
Lemma addressable_agree : forall LIB m m' b,
  magree (lib_addr LIB) m m' -> In b LIB -> addressable m (blk_addr b) (blk_size b) -> addressable m' (blk_addr b) (blk_size b).
Proof.
  intros LIB m m' b AG Hb (Hn & A0 & A8 & B & W). pose proof (shadow_of_length (blk_size b) Hn) as SL.
  assert (R : forall a, in_range (sh (blk_addr b)) (nsh (blk_size b)) a -> lib_addr LIB a).
  { intros a Ha. right; right. exists b. split; [exact Hb|]. unfold in_range in Ha. exact Ha. }
  split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
  - eapply bytes_at_agree; [exact AG| exact B|]. intros a Ha. apply R. unfold in_range in *. lia.
  - eapply wr_at_agree; [exact AG| exact W|]. intros a Ha. apply R. unfold in_range in *. lia.
Qed.
Lemma lib_shad_frame : forall LIB m m', lib_shad LIB m -> magree (lib_addr LIB) m m' -> lib_shad LIB m'.
Proof.
  intros LIB m m' SH AG. unfold lib_shad in *. apply Forall_forall. intros b Hb.
  eapply addressable_agree; [exact AG| exact Hb| exact (proj1 (Forall_forall _ _) SH b Hb)].
Qed.
Lemma lib_blocks_frame : forall LIB m m' i, lib_blocks_inited LIB m i -> magree (lib_addr LIB) m m' -> lib_blocks_inited LIB m' i.
Proof.
  intros LIB m m' i B AG. unfold lib_blocks_inited in *.
  destruct B as (X & C & (E & C5 & CE) & SH).
  split; [eapply CTX_blocks_frame; eauto|]. split; [eapply ERR_chain_frame; eauto|].
  split.
  2:{ eapply lib_shad_frame; [exact SH|]. eapply magree_mono; [exact AG|].
      assert (SUBc : forall b, In b (chain_blocks (li_chain i)) -> In b LIB).
      { pose proof C as (I1 & _ & _ & I2 & _ & _ & I3 & _ & _ & I4 & _ & I6 & _ & _). intros b Hb. unfold chain_blocks in Hb. cbn in Hb.
        destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption. }
      intros a [HXa|[(b & Hb & R)|(b & Hb & R)]]; [left; exact HXa| right; left| right; right]; exists b; split; auto. }
  exists E. split; [| exact CE].
  destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _ & _).
  destruct (ec_es (li_chain i)) as [[p5 a5] n5] eqn:E5. cbn [blk_addr blk_size fst snd] in *.
  eapply ERRST_agree; [exact AG | exact C5 | solve_in_block I5 Z5].
Qed.

Lemma LIBST_frame : forall st LIB m m', LIBST st LIB m -> magree (lib_addr LIB) m m' -> LIBST st LIB m'.
Proof.
  intros [|i] LIB m m' H AG; cbn [LIBST] in *.
  - destruct H as (-> & P & M). split; [reflexivity|]. split.
    + intros a Ha.
      assert (R : 0 <= a < 2^64).
      { revert Ha. unfold LIBX0. cbn [rin_ivs fst snd]. lia. }
      eapply none_agree; [exact AG | exact R | left; apply LIBX0_sub_LIBX; exact Ha | apply P; exact Ha].
    + eapply musl0_frame; eauto.
  - destruct H as (S & B & SZ). split; [eapply lib_statics_frame; eauto | split; [eapply lib_blocks_frame; eauto| exact SZ]].
Qed.

(* [comment removed for export] *)
Lemma magree_of_amagree : forall LIB m m',
  amagree (fun a => rin_ivs LIBX a \/ in_lblock LIB a \/ in_lblock_sh LIB a) m m' -> magree (lib_addr LIB) m m'.
Proof. intros LIB m m' H a Ha Hr. apply H; [exact Ha|]. exact Hr. Qed.

(* [comment removed for export] *)
Definition LIBXP : list (Z * Z) := [(A_next_key + 4, A_key_lock)].
Definition LIBXT : list (Z * Z) := LIBX ++ LIBXP.
Lemma LIBX_sub_LIBXT : forall a, rin_ivs LIBX a -> rin_ivs LIBXT a.
Proof. intros a H. unfold LIBXT. apply (proj2 (rin_ivs_app _ _ _)). left. exact H. Qed.
Lemma magree_of_amagreeT : forall LIB m m',
  amagree (fun a => rin_ivs LIBXT a \/ in_lblock LIB a \/ in_lblock_sh LIB a) m m' -> magree (lib_addr LIB) m m'.
Proof.
  intros LIB m m' H a Ha Hr. apply H; [exact Ha|].
  destruct Hr as [Hr|Hr]; [left; apply LIBX_sub_LIBXT; exact Hr| right; exact Hr].
Qed.

End LIB.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AL_FRAMES : nat := 752%nat.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ACOST_BYTES : Z := 2^25.
(* [comment removed for export] *)
Definition acost (H : asr) (N : Z) : Z := as_Cm H ACOST_BYTES + as_Cf H ACOST_BYTES.

(* [comment removed for export] *)
Definition atr_ok (H : asr) : Prop :=
  Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) LIB_TRACES.

Definition ECHL : alib :=
  {| al_st := libst ;
     al_fresh := Fresh ;
     al_is_fresh := is_fresh ;
     al_LIBST := LIBST ;
     al_LIBX0 := LIBX0 ;
     al_LIBX := LIBXT ;                 (* [comment removed for export] *)
     al_frames := AL_FRAMES ;
     al_cost := fun H N => acost H N ;
     al_PF := [] ;
     al_tr_ok := fun H => atr_ok H |}.
