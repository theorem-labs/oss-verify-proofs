(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_leaves.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_quar_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qput.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qenqueue.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_asan_free.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malstate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freelift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_geo0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_fkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeC.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeD.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeF.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeG.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pop24 (Σ : rtsA) (cal : list Z) (jB : nat) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? 24 then upd_reg (pr Σ 24) jB CkBatch else pr Σ c') (fun c' => if c' =? 24 then cal else ca Σ c')
    (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fsx Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).
Definition enq_new (Σ : rtsA) (cal : list Z) (jB : nat) (M n : Z) : rtsA :=
  set_ql (pop24 Σ cal jB) (ql Σ ++ [(p_abeg (l_SB (lay Σ)) 24 jB, [(M, n)])]).

(* [comment removed for export] *)
Definition pend_ok (Σ : rtsA) (c : Z) (i : nat) (n : Z) : Prop :=
  1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkQuar n)
  /\ ~ In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) (map fst (qents Σ))
  /\ (forall c' i' n', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some (CkQuar n') -> (c' <> c \/ i' <> i) ->
        In (p_abeg (l_SB (lay Σ)) c' i' + rz_size n' - 16, n') (qents Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qents Σ)).

Lemma pend_free_p : forall Σ m c i n p D', ART_A Σ m -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  pend_ok (free_p Σ c i n p D') c i n.
Proof.
  intros Σ m c i n p D' HA Hc Hn. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (RC1 & RC2)).
  split; [exact Hc|]. split.
  { cbn [pr free_p]. destruct (Z.eqb_spec c c) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st].
    rewrite nth_error_upd_ck, Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt _ _) (proj1 (nth_error_Some _ _) ltac:(rewrite Hn; discriminate))). reflexivity. }
  split; [exact (new_ent_fresh Σ m c i n HA Hc Hn)|]. split.
  - intros c' i' n' Hc' Hi' Hne. cbn [pr free_p lay qents] in *. destruct (fp_st Σ c i n Hc c' i' _ Hi') as [(-> & -> & _)|(_ & Hi0)].
    + destruct Hne as [X|X]; exfalso; apply X; reflexivity.
    + exact (RC1 c' i' n' Hc' Hi0).
  - intros s Hs Hq. exact (RC2 s Hs Hq).
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs
  R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc
  R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit
  RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2
  RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pop24 (Σ : rtsA) (cal : list Z) (jB : nat) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? 24 then upd_reg (pr Σ 24) jB CkBatch else pr Σ c') (fun c' => if c' =? 24 then cal else ca Σ c')
    (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fs0 Σ) (fs2 Σ) (fsx Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ).
Definition enq_new (Σ : rtsA) (cal : list Z) (jB : nat) (M n : Z) : rtsA :=
  set_ql (pop24 Σ cal jB) (ql Σ ++ [(p_abeg (l_SB (lay Σ)) 24 jB, [(M, n)])]).

(* [comment removed for export] *)
Definition pend_ok (Σ : rtsA) (c : Z) (i : nat) (n : Z) : Prop :=
  1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkQuar n)
  /\ ~ In (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) (map fst (qents Σ))
  /\ (forall c' i' n', 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some (CkQuar n') -> (c' <> c \/ i' <> i) ->
        In (p_abeg (l_SB (lay Σ)) c' i' + rz_size n' - 16, n') (qents Σ))
  /\ (forall s, In s (sec Σ) -> s_quar s = true -> In (s_mb s + 6128, s_n s) (qents Σ)).

Lemma pend_free_p : forall Σ m c i n p D', ART_A Σ m -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n) ->
  pend_ok (free_p Σ c i n p D') c i n.
Proof.
  intros Σ m c i n p D' HA Hc Hn. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (RC1 & RC2)).
  split; [exact Hc|]. split.
  { cbn [pr free_p]. destruct (Z.eqb_spec c c) as [_|X]; [|exfalso; apply X; reflexivity]. unfold upd_reg. cbn [r_st].
    rewrite nth_error_upd_ck, Nat.eqb_refl. rewrite (proj2 (Nat.ltb_lt _ _) (proj1 (nth_error_Some _ _) ltac:(rewrite Hn; discriminate))). reflexivity. }
  split; [exact (new_ent_fresh Σ m c i n HA Hc Hn)|]. split.
  - intros c' i' n' Hc' Hi' Hne. cbn [pr free_p lay qents] in *. destruct (fp_st Σ c i n Hc c' i' _ Hi') as [(-> & -> & _)|(_ & Hi0)].
    + destruct Hne as [X|X]; exfalso; apply X; reflexivity.
    + exact (RC1 c' i' n' Hc' Hi0).
  - intros s Hs Hq. exact (RC2 s Hs Hq).
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
