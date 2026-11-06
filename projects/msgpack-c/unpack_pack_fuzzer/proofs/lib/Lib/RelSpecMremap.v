(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import RelSpec.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Lemma syscall_spec_216 : forall i m o,
  bv_unsigned (in_sysno i) = 216%Z ->
  syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Definition mremap_out (old osz nsz : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
  let h := m_vmmaps m in
  let old_nZ := page_round_up_Z (bv_unsigned osz) in
  let new_nZ := page_round_up_Z (bv_unsigned nsz) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  (old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (old_nZ <> new_nZ /\
      ( (exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
      \/ ((new_nZ < old_nZ)%Z /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
      \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
          /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
      \/ ((old_nZ < new_nZ)%Z /\ exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true
          /\ o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))).

Lemma mremap_maymove_outcome : forall old osz nsz flags i m o,
  bv_unsigned flags = MREMAP_MAYMOVE ->
  (bv_unsigned old mod page_size = 0)%Z ->
  page_align_is0_b nsz = false -> page_align_is0_b osz = false ->
  let h := m_vmmaps m in
  let old_nZ := page_round_up_Z (bv_unsigned osz) in
  let old_n := Z_to_bv 64 old_nZ in
  mremap_source_b h old old_n old_nZ = true -> mremap_backing_uniform_b m old old_n = true ->
  mremap_spec old osz nsz flags i m o <-> mremap_out old osz nsz m o.
Proof.
  intros old osz nsz flags i m o Hfl Hal Hn Ho. cbv zeta. intros Hsrc Hbk.
  unfold mremap_spec. rewrite Hfl. change (negb (MREMAP_MAYMOVE =? MREMAP_MAYMOVE)%Z) with false. cbn iota.
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hn, Ho. unfold mremap_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Hbk in *; cbn [andb negb] in *; inv_sys.
    + destruct (Z.eqb_spec (page_round_up_Z (bv_unsigned osz)) (page_round_up_Z (bv_unsigned nsz))) as [E|NE]; inv_sys.
      * left. split; [exact E | reflexivity].
      * right. split; [exact NE|]. left. eexists; split; [eassumption | reflexivity].
      * right. split; [exact NE|].
        destruct (Z.ltb_spec (page_round_up_Z (bv_unsigned nsz)) (page_round_up_Z (bv_unsigned osz))) as [LT|GE]; inv_sys.
        -- right; left. split; [exact LT | reflexivity].
        -- destruct (mremap_inplace_grow_b m old _ _ _ _) eqn:G; inv_sys.
           ++ right; right; left. split; [lia|]. split; [reflexivity | reflexivity].
           ++ right; right; right. split; [lia|]. eexists; split; [eassumption | reflexivity].
           ++ right; right; right. split; [lia|]. eexists; split; [eassumption | reflexivity].
    + destruct (Z.eqb_spec (page_round_up_Z (bv_unsigned osz)) (page_round_up_Z (bv_unsigned nsz))) as [E|NE]; inv_sys.
      destruct (Z.ltb_spec (page_round_up_Z (bv_unsigned nsz)) (page_round_up_Z (bv_unsigned osz))) as [LT|GE]; inv_sys.
      destruct (mremap_inplace_grow_b m old _ _ _ _) eqn:G; inv_sys.
  - intros [[E ->] | [NE [(e & He & ->) | [[LT ->] | [(LT & G & ->) | (LT & dst & Hd & ->)]]]]].
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_eq _ _) E). split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. left.
      eexists _, _, _, _. split; [exists e; split; [exact He | reflexivity]|]. split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      rewrite (proj2 (Z.ltb_lt _ _) LT).
      eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      replace (page_round_up_Z (bv_unsigned nsz) <? page_round_up_Z (bv_unsigned osz))%Z with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite G. left. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      replace (page_round_up_Z (bv_unsigned nsz) <? page_round_up_Z (bv_unsigned osz))%Z with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (mremap_inplace_grow_b m old _ _ _ _).
      * right. eexists _, _, _, _. split; [exists dst; split; [exact Hd | reflexivity]|].
        split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
      * eexists _, _, _, _. split; [exists dst; split; [exact Hd | reflexivity]|].
        split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.
