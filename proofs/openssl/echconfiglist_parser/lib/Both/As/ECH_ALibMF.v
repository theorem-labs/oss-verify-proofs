(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_Iface ECH_ALib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lib_addr_mf (LIB : list block) (a : Z) : Prop := lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1).
Definition lib_addr_mv (LIB : list block) (a : Z) : Prop :=
  lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1) /\ ~ (A_vdso_func <= a < A_vdso_func + 8).

Lemma magree_mf_of_lib : forall LIB m m', magree (lib_addr LIB) m m' -> magree (lib_addr_mf LIB) m m'.
Proof. intros LIB m m' AG. eapply magree_mono; [exact AG|]. intros a [Ha _]. exact Ha. Qed.
Lemma magree_mv_of_mf : forall LIB m m', magree (lib_addr_mf LIB) m m' -> magree (lib_addr_mv LIB) m m'.
Proof. intros LIB m m' AG. eapply magree_mono; [exact AG|]. intros a (Ha & Hb & _). split; assumption. Qed.
Lemma magree_mv_mono : forall L1 L2 m m', (forall b, In b L1 -> In b L2) -> magree (lib_addr_mv L2) m m' -> magree (lib_addr_mv L1) m m'.
Proof.
  intros L1 L2 m m' SUB AG. eapply magree_mono; [exact AG|]. intros a (Ha & Hb & Hc). split; [| split; assumption].
  destruct Ha as [HX|[(b & Hin & R)|(b & Hin & R)]]; [left; exact HX| right; left| right; right]; exists b; split; auto.
Qed.

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
Local Ltac solve_in_block_mv HIN HSZ :=
  intros a Ha; unfold in_range in Ha; rewrite ?HSZ in Ha;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul blk_addr blk_size fst snd] in *;
  split; [ right; left; eexists; split; [exact HIN|]; rewrite ?HSZ; cbn [blk_addr blk_size fst snd]; unfold MUTEX_SIZE in *; lia
         | unfold arange, MUTEX_SIZE, A_mem_inited, A_vdso_func, AIMG_TOP in *; split; lia ].

Lemma none_on_agree_mv : forall R m m' A n, magree R m m' -> none_on m A n -> (forall a, in_range A n a -> R a) -> 0 <= A -> A + n <= 2^64 -> none_on m' A n.
Proof.
  intros R m m' A n AG H HR HA HN a Ha. eapply none_agree; [exact AG | lia | apply HR; exact Ha | apply H; exact Ha].
Qed.
Local Ltac frame_conj AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX_mv]
        | eapply none_on_agree_mv; [exact AG | eassumption | solve_in_LIBX_mv | | ];
          unfold A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
            A_defctx_exmeth_bio, A_tevent_once, A_base_inited, A_stopped, A_in_init_config_key, A_base_once, A_base_ret, A_load_strings_once, A_load_strings_ret,
            A_optsdone_lock, A_init_lock, A_optsdone, A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main, LIBKEY0; lia
        | assumption ].
Local Ltac frame_group AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj AG.

Lemma musl0_frame_mv : forall LIB m m', musl0 m -> magree (lib_addr_mv LIB) m m' -> musl0 m'.
Proof. intros LIB m m' S AG. unfold musl0 in *. frame_group AG. Qed.
Lemma CTX_statics_frame_mv : forall LIB m m' x, CTX_statics m x -> magree (lib_addr_mv LIB) m m' -> CTX_statics m' x.
Proof. intros LIB m m' x S AG. unfold CTX_statics in *. frame_group AG. Qed.
Lemma CTX_keys_frame_mv : forall LIB m m', CTX_keys m -> magree (lib_addr_mv LIB) m m' -> CTX_keys m'.
Proof. intros LIB m m' S AG. unfold CTX_keys in *. frame_group AG. Qed.
Lemma EXLOCK_frame_mv : forall LIB m m' b, EXLOCK LIB m b -> magree (lib_addr_mv LIB) m m' -> EXLOCK LIB m' b.
Proof.
  intros LIB m m' b (I1 & Z1 & R1 & C1) AG. unfold EXLOCK, MUTEX in *. destruct b as [[p1 a1] n1]. cbn [blk_addr blk_size fst snd] in *.
  split; [exact I1|]. split; [exact Z1|]. split; [exact R1|]. eapply rw_cells_agree; [exact AG | exact C1 | solve_in_block_mv I1 Z1].
Qed.
Lemma CTX_blocks_frame_mv : forall LIB m m' x, CTX_blocks LIB m x -> magree (lib_addr_mv LIB) m m' -> CTX_blocks LIB m' x.
Proof. intros LIB m m' x [E O] AG. split; [eapply EXLOCK_frame_mv; eauto | exact O]. Qed.
Lemma CTX_fresh_frame_mv : forall LIB m m', CTX_fresh m -> magree (lib_addr_mv LIB) m m' -> CTX_fresh m'.
Proof.
  intros LIB m m' S AG. unfold CTX_fresh in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end;
  first [ eapply musl0_frame_mv; eassumption | frame_conj AG ].
Qed.
Lemma CTXPH_frame_mv : forall LIB m m' ph, CTXPH LIB m ph -> magree (lib_addr_mv LIB) m m' -> CTXPH LIB m' ph.
Proof.
  intros LIB m m' [|x] C AG; cbn [CTXPH] in *.
  - eapply CTX_fresh_frame_mv; eauto.
  - destruct C as [CS CB]. split; [eapply CTX_statics_frame_mv; eauto| eapply CTX_blocks_frame_mv; eauto].
Qed.

(* [comment removed for export] *)
Lemma CTXPH_frame_mf : forall LIB m m' ph, CTXPH LIB m ph -> magree (lib_addr_mf LIB) m m' -> CTXPH LIB m' ph.
Proof. intros LIB m m' ph C AG. eapply CTXPH_frame_mv; [exact C| apply magree_mv_of_mf; exact AG]. Qed.
Lemma CTX_keys_frame_mf : forall LIB m m', CTX_keys m -> magree (lib_addr_mf LIB) m m' -> CTX_keys m'.
Proof. intros LIB m m' C AG. eapply CTX_keys_frame_mv; [exact C| apply magree_mv_of_mf; exact AG]. Qed.
Lemma CTXPH_frame_mf' : forall LIB m m' ph,
  CTXPH LIB m ph -> magree (fun a => lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1)) m m' -> CTXPH LIB m' ph.
Proof. intros LIB m m' ph C AG. eapply CTXPH_frame_mf; [exact C| exact AG]. Qed.

(* [comment removed for export] *)
Lemma CTXPH_mono : forall L L' (SUB : forall b, In b L -> In b L') m ph, CTXPH L m ph -> CTXPH L' m ph.
Proof.
  intros L L' SUB m [|x0] C; cbn [CTXPH] in *; [exact C|]. destruct C as [CS [EX (po & pi & O1 & O2)]].
  split; [exact CS|]. split; [| exists po, pi; split; apply SUB; assumption].
  destruct EX as (E1 & E2 & E3 & E4). split; [apply SUB; exact E1|]. split; [exact E2|]. split; [exact E3| exact E4].
Qed.
End HCW.
