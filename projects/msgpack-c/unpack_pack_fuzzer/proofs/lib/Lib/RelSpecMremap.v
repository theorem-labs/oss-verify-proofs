(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (mremap_out answers EINVAL for a new length over TASK_SIZE, grows in place when there is room above the source (mremap_inplace_room_b, a failing charge being a refusal) and otherwise moves to Linux's placement (mremap_dst_ok); mremap_maymove_outcome re-proved for it). *)
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

(* LPS 08b1429: a new length over TASK_SIZE is -EINVAL before any lookup
   ([check_mremap_params]); a grow with room above the source stays in place (a failing
   charge is a refusal), and one without room moves to Linux's preference-free placement
   ([Mremap.mremap_dst_ok]). *)
Definition mremap_out (old osz nsz : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
  let h := m_vmmaps m in
  let old_nZ := page_round_up_Z (bv_unsigned osz) in
  let new_nZ := page_round_up_Z (bv_unsigned nsz) in
  let old_n := Z_to_bv 64 old_nZ in
  let new_n := Z_to_bv 64 new_nZ in
  ((TASK_SIZE < new_nZ)%Z /\ o = Ok (mkEffect (errno_ret EINVAL) [] []) m [])
  \/ ((new_nZ <= TASK_SIZE)%Z /\
  ((old_nZ = new_nZ /\ o = Ok (mkEffect old [] []) m [])
  \/ (old_nZ <> new_nZ /\
      ( (exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [])
      \/ ((new_nZ < old_nZ)%Z /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
      \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
          /\ o = Ok (mremap_inplace_effect old old_n new_n old_nZ new_nZ) (mremap_model_next m old old_n old new_n) [])
      \/ ((old_nZ < new_nZ)%Z /\ mremap_inplace_room_b m old old_n new_n old_nZ new_nZ = false
          /\ exists dst, mremap_dst_ok m old_nZ new_nZ old old_n dst new_n
          /\ o = Ok (mremap_move_effect old old_n dst old_nZ new_nZ) (mremap_model_next m old old_n dst new_n) []))))).

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
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. rewrite Hn. unfold mremap_out.
  destruct (Z.ltb_spec TASK_SIZE (page_round_up_Z (bv_unsigned nsz))) as [TS|TS].
  { sys_unfold. split.
    - destruct o as [x m' evs|]; intros H; inv_sys. left. split; [exact TS | reflexivity].
    (* [check_mremap_params]' TASK_SIZE refusal is [err_ret EINVAL], i.e. a bare
       [pure]: after [sys_unfold] the goal is an equation, with no [bind] to split. *)
    - intros [[_ ->] | [TS' _]]; [|lia]. reflexivity. }
  rewrite Ho. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hsrc, Hbk in *; cbn [andb negb] in *; inv_sys.
    + right. split; [exact TS|].
      destruct (Z.eqb_spec (page_round_up_Z (bv_unsigned osz)) (page_round_up_Z (bv_unsigned nsz))) as [E|NE]; inv_sys.
      * left. split; [exact E | reflexivity].
      * right. split; [exact NE|]. left. eexists; split; [eassumption | reflexivity].
      * right. split; [exact NE|].
        destruct (Z.ltb_spec (page_round_up_Z (bv_unsigned nsz)) (page_round_up_Z (bv_unsigned osz))) as [LT|GE]; inv_sys.
        -- right; left. split; [exact LT | reflexivity].
        -- destruct (mremap_inplace_room_b m old _ _ _ _) eqn:Rm; inv_sys.
           (* RETRACTION of the cause first recorded here, which was an unmeasured
              claim about Ltac: [inv_sys]'s [H : _ /\ _ |- _ => destruct H]
              (Lib/RelSpec.v:103) does NOT see through a definition, so it leaves
              [Mremap.mremap_dst_ok] WHOLE and [eassumption] below does find it.
              Measured: the model's [inv_ok] (75d69e00 Checks/Sys/Prelude.v:788-804)
              carries that identical clause, yet the model's own compiled proof still
              destructs the hypothesis by hand at 75d69e00 Checks/Sys/Mm/Mremap.v:441-444
              -- a [lazymatch] that could not have found it had [inv_ok] split it.
              So the cause of this block's failure is NOT the conjunction, and is not
              yet known.  What IS established: the grow branch is sound (this proof
              destructs [mremap_inplace_room_b] directly, so the unfold below yields
              exactly [mremap_final_budget_b … = true]), and both [lia]s have [NE] and
              [GE].  An [all: … first [… | …]] hides WHICH of the two goals and WHICH
              step fails; these explicit bullets make the next error name it. *)
           ++ (* room above the source: Linux expands in place *)
              right; right; left. split; [lia|]. split; [|reflexivity].
              (* [rewrite] matches SYNTACTICALLY, and [Rm]'s LHS was elaborated
                 against the occurrence in H while this goal comes from
                 [mremap_out]'s own lets -- convertible, not necessarily syntactically
                 equal, which is rule 11c's "Found no subterm matching" shape.
                 [andb_true_intro] + [exact]/[assumption] work UP TO CONVERSION, so
                 this closes the same goal without a syntactic match.  Load-bearing:
                 do not tidy it back into [rewrite Rm; cbn [andb]]. *)
              unfold mremap_inplace_grow_b.
              apply andb_true_intro; split; [exact Rm | assumption].
           ++ (* no room: the move to Linux's preference-free placement.
                 At 75d69e00 the [mremap_out] let that carries this conjunct is
                 SYNTACTICALLY the term [destruct ... eqn:Rm] replaced, so the
                 goal arrives already reduced to [false = false] and [exact Rm]
                 reports "expected false = false".  Keep both: [exact Rm] for a
                 shape where the occurrence survives, [reflexivity] for the one
                 where [destruct] consumed it.  Neither weakens the goal. *)
              right; right; right. split; [lia|]. split; [first [exact Rm | reflexivity]|].
              eexists. split; [first [eassumption | split; eassumption] | reflexivity].
    + destruct (Z.eqb_spec (page_round_up_Z (bv_unsigned osz)) (page_round_up_Z (bv_unsigned nsz))) as [E|NE]; inv_sys.
      destruct (Z.ltb_spec (page_round_up_Z (bv_unsigned nsz)) (page_round_up_Z (bv_unsigned osz))) as [LT|GE]; inv_sys.
      destruct (mremap_inplace_room_b m old _ _ _ _) eqn:Rm; inv_sys.
  - intros [[TS' _] | [_ [[E ->] | [NE [(e & He & ->) | [[LT ->] | [(LT & G & ->) | (LT & Rm & dst & Hd & ->)]]]]]]]; [lia| | | | |].
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_eq _ _) E). split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. left.
      eexists _, _, _, _. split; [exists e; split; [exact He | reflexivity]|]. split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      rewrite (proj2 (Z.ltb_lt _ _) LT).
      eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + unfold mremap_inplace_grow_b in G. apply andb_prop in G as [Rm Bd].
      eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      replace (page_round_up_Z (bv_unsigned nsz) <? page_round_up_Z (bv_unsigned osz))%Z with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Rm.
      eexists _, _, _, _. split; [exists tt; split; [exact Bd | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
    + eexists _, _, _, _. split; [reflexivity|]. rewrite Hsrc, Hbk. cbn [andb negb].
      rewrite (proj2 (Z.eqb_neq _ _) NE). split; [|reflexivity]. right.
      replace (page_round_up_Z (bv_unsigned nsz) <? page_round_up_Z (bv_unsigned osz))%Z with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Rm.
      eexists _, _, _, _. split; [exists dst; split; [exact Hd | reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.
