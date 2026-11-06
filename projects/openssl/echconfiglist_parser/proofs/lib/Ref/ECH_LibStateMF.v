(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition lib_addr_mf (LIB : list block) (a : Z) : Prop := lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1).

Lemma magree_mf_of_lib : forall LIB m m', magree (lib_addr LIB) m m' -> magree (lib_addr_mf LIB) m m'.
Proof. intros LIB m m' AG. eapply magree_mono; [exact AG|]. intros a [Ha _]. exact Ha. Qed.

Local Ltac in_LIBX_tac a Ha :=
  left; apply (proj1 (in_ivs_b_spec LIBX a));
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold LIBX, LIBX0, A_malloc_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_master_once_ret,
    A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_tevent_once, A_stopped, A_base_inited, A_base_once, A_optsdone,
    A_optsdone_lock, A_in_init_config_key, A_load_strings_once, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in *;
  cbn [in_ivs_b fst snd];
  repeat (rewrite Bool.orb_true_iff; first [left; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia | right]).
Local Ltac not_mf_tac Ha :=
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold A_malloc_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_master_once_ret,
    A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_tevent_once, A_stopped, A_base_inited, A_base_once, A_optsdone,
    A_optsdone_lock, A_in_init_config_key, A_load_strings_once, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in *; lia.
Local Ltac solve_in_LIBX_mf :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [in_LIBX_tac a Ha| not_mf_tac Ha].

Local Ltac solve_in_block_mf HIN HSZ HRR :=
  intros a Ha; unfold in_range in Ha; rewrite ?HSZ in Ha;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul blk_addr blk_size fst snd] in *;
  split; [ right; eexists; split; [exact HIN|]; rewrite ?HSZ; cbn [blk_addr blk_size fst snd]; unfold ERRST_SIZE, MUTEX_SIZE, O_MKEY_ERR in *; lia
         | unfold rblock_range, MUTEX_SIZE, A_mem_inited in *; lia ].

Lemma none_on_agree_mf : forall R m m' A n, magree R m m' -> none_on m A n -> (forall a, in_range A n a -> R a) -> 0 <= A -> A + n <= 2^64 -> none_on m' A n.
Proof.
  intros R m m' A n AG H HR HA HN a Ha. eapply none_agree; [exact AG | lia | apply HR; exact Ha | apply H; exact Ha].
Qed.
Local Ltac frame_conj AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX_mf]
        | eapply none_on_agree_mf; [exact AG | eassumption | solve_in_LIBX_mf | | ];
          unfold A_defctx_exmeth_bio, A_tsd_main, A_stopped, A_key_lock; lia
        | assumption ].
Local Ltac frame_group AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj AG.

Lemma CTX_statics_frame_mf : forall LIB m m' x, CTX_statics m x -> magree (lib_addr_mf LIB) m m' -> CTX_statics m' x.
Proof. intros LIB m m' x S AG. unfold CTX_statics in *. frame_group AG. Qed.

Lemma EXLOCK_frame_mf : forall LIB m m' b, EXLOCK LIB m b -> magree (lib_addr_mf LIB) m m' -> EXLOCK LIB m' b.
Proof.
  intros LIB m m' b (I1 & Z1 & R1 & C1) AG. unfold EXLOCK, MUTEX in *. destruct b as [[p1 a1] n1]. cbn [blk_addr blk_size fst snd] in *.
  split; [exact I1|]. split; [exact Z1|]. split; [exact R1|]. eapply rw_cells_agree; [exact AG | exact C1 | solve_in_block_mf I1 Z1 R1].
Qed.
Lemma CTX_blocks_frame_mf : forall LIB m m' x, CTX_blocks LIB m x -> magree (lib_addr_mf LIB) m m' -> CTX_blocks LIB m' x.
Proof. intros LIB m m' x [E O] AG. split; [eapply EXLOCK_frame_mf; eauto | exact O]. Qed.
Lemma CTX_fresh_frame_mf : forall LIB m m', CTX_fresh m -> magree (lib_addr_mf LIB) m m' -> CTX_fresh m'.
Proof.
  intros LIB m m' S AG. unfold CTX_fresh in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end;
  (eapply none_on_agree_mf; [exact AG | eassumption | solve_in_LIBX_mf | | ]);
  unfold A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_load_strings_once, A_optsdone_lock, A_optsdone,
    A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main; lia.
Qed.
Lemma CTXPH_frame_mf : forall LIB m m' ph, CTXPH LIB m ph -> magree (lib_addr_mf LIB) m m' -> CTXPH LIB m' ph.
Proof.
  intros LIB m m' [|x] C AG; cbn [CTXPH] in *.
  - eapply CTX_fresh_frame_mf; eauto.
  - destruct C as [CS CB]. split; [eapply CTX_statics_frame_mf; eauto| eapply CTX_blocks_frame_mf; eauto].
Qed.

(* [comment removed for export] *)
Lemma CTXPH_frame_mf' : forall LIB m m' ph,
  CTXPH LIB m ph -> magree (fun a => lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1)) m m' -> CTXPH LIB m' ph.
Proof. intros LIB m m' ph C AG. eapply CTXPH_frame_mf; [exact C| exact AG]. Qed.

(* [comment removed for export] *)
Definition lib_addr_mv (LIB : list block) (a : Z) : Prop :=
  lib_addr LIB a /\ ~ (A_mem_inited <= a < A_mem_inited + 1) /\ ~ (A_vdso_func <= a < A_vdso_func + 8).
Local Ltac not_mv_tac Ha :=
  unfold in_range in Ha; cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in Ha;
  unfold A_malloc_impl, A_destructor_key, A_vdso_func, A_mem_inited, A_err_string_once, A_master_once_ret,
    A_defctx_inited, A_defctx_exlock, A_defctx_exmeth_bio, A_tevent_once, A_stopped, A_base_inited, A_base_once, A_optsdone,
    A_optsdone_lock, A_in_init_config_key, A_load_strings_once, A_td_tsd, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key,
    A_key_lock, A_tsd_main in *; lia.
Local Ltac solve_in_LIBX_mv :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [in_LIBX_tac a Ha| split; not_mv_tac Ha].
Local Ltac solve_in_block_mv HIN HSZ HRR :=
  intros a Ha; unfold in_range in Ha; rewrite ?HSZ in Ha;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul blk_addr blk_size fst snd] in *;
  split; [ right; eexists; split; [exact HIN|]; rewrite ?HSZ; cbn [blk_addr blk_size fst snd]; unfold ERRST_SIZE, MUTEX_SIZE, O_MKEY_ERR in *; lia
         | unfold rblock_range, MUTEX_SIZE, A_mem_inited, A_vdso_func in *; lia ].
Local Ltac frame_conj_mv AG :=
  first [ eapply rw_cells_agree; [exact AG | eassumption | solve_in_LIBX_mv]
        | eapply none_on_agree_mf; [exact AG | eassumption | solve_in_LIBX_mv | | ];
          unfold A_defctx_exmeth_bio, A_tsd_main, A_stopped, A_key_lock; lia
        | assumption ].
Local Ltac frame_group_mv AG :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end; frame_conj_mv AG.
Lemma CTX_statics_frame_mv : forall LIB m m' x, CTX_statics m x -> magree (lib_addr_mv LIB) m m' -> CTX_statics m' x.
Proof. intros LIB m m' x S AG. unfold CTX_statics in *. frame_group_mv AG. Qed.
Lemma EXLOCK_frame_mv : forall LIB m m' b, EXLOCK LIB m b -> magree (lib_addr_mv LIB) m m' -> EXLOCK LIB m' b.
Proof.
  intros LIB m m' b (I1 & Z1 & R1 & C1) AG. unfold EXLOCK, MUTEX in *. destruct b as [[p1 a1] n1]. cbn [blk_addr blk_size fst snd] in *.
  split; [exact I1|]. split; [exact Z1|]. split; [exact R1|]. eapply rw_cells_agree; [exact AG | exact C1 | solve_in_block_mv I1 Z1 R1].
Qed.
Lemma CTX_blocks_frame_mv : forall LIB m m' x, CTX_blocks LIB m x -> magree (lib_addr_mv LIB) m m' -> CTX_blocks LIB m' x.
Proof. intros LIB m m' x [E O] AG. split; [eapply EXLOCK_frame_mv; eauto | exact O]. Qed.
Lemma CTX_fresh_frame_mv : forall LIB m m', CTX_fresh m -> magree (lib_addr_mv LIB) m m' -> CTX_fresh m'.
Proof.
  intros LIB m m' S AG. unfold CTX_fresh in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with |- _ /\ _ => split end;
  (eapply none_on_agree_mf; [exact AG | eassumption | solve_in_LIBX_mv | | ]);
  unfold A_destructor_key, A_defctx_inited, A_tevent_once, A_base_inited, A_load_strings_once, A_optsdone_lock, A_optsdone,
    A_td_cancelbuf, A_keys, A_key_lock, A_tsd_main; lia.
Qed.
Lemma CTXPH_frame_mv : forall LIB m m' ph, CTXPH LIB m ph -> magree (lib_addr_mv LIB) m m' -> CTXPH LIB m' ph.
Proof.
  intros LIB m m' [|x] C AG; cbn [CTXPH] in *.
  - eapply CTX_fresh_frame_mv; eauto.
  - destruct C as [CS CB]. split; [eapply CTX_statics_frame_mv; eauto| eapply CTX_blocks_frame_mv; eauto].
Qed.
End HCW.
