(** * Bridge.Infl.IArmType — pair I7 of PAIRS.md: TYPE and TYPEDO.

    TYPE falls through to TYPEDO without setting the mode (flush is [Z_NO_FLUSH]).  TYPEDO
    either ends the stream (last block seen: BYTEBITS, then CHECK) or reads the three block
    header bits and moves to STORED, LEN_ with the fixed tables ([IFixed]), TABLE, or BAD. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IFixed IArmTypeKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma arm_TYPEDO_ok : forall c w q,
  ctx_rel FL c -> icore w q -> RI.q_mode q = RI.M_TYPEDO \/ RI.q_mode q = RI.M_TYPE ->
  step_ok (IA.arm_TYPEDO IS.ivar_ref FL w) (RI.inf_TYPEDO c q).
Proof.
  intros c w q [Hfl _] H Hm.
  assert (Hq : RI.q_mode q <> RI.M_HEAD) by (destruct Hm as [E|E]; rewrite E; discriminate).
  unfold IA.arm_TYPEDO, RI.inf_TYPEDO. cbv zeta. s5red.
  rewrite (icore_last_eq w q H), Hfl, fl_trees_s5, fl_trees_rt.
  destruct (RI.h_last (RI.s_hdr (RI.q_st q)) =? 0) eqn:EL; cbn [negb].
  - (* last = 0: the three block-header bits *)
    destruct (RI.inf_nb 3 (RI.q_br q)) as [b|b] eqn:Enb.
    2: { apply step_leave_ok. exact (icore_ret w q H). }
    destruct (icore_needbits w q _ b 3 H eq_refl ltac:(lia) Enb) as (E3 & H1 & L3).
    s5step E3.
    s5step (icore_bits _ _ b 1 H1 eq_refl ltac:(lia)).
    pose proof (icore_last _ _ (RB.br_bits_of 1 b) H1) as H2.
    destruct (icore_dropbits _ _ b 1 H2 eq_refl ltac:(lia)) as (E4 & H3).
    s5step E4.
    s5step (icore_bits _ _ (RB.br_dropbits 1 b) 2 H3 eq_refl ltac:(lia)).
    assert (L2 : 0 <= 2 <= RB.br_bits (RB.br_dropbits 1 b))
      by (cbn [RB.br_bits RB.br_dropbits]; lia).
    destruct (RB.br_bits_of 2 (RB.br_dropbits 1 b) =? 0) eqn:T0; s5red.
    + (* stored *)
      pose proof (icore_modez _ _ RI.M_STORED IS.STORED H3 eq_refl Hq) as H4.
      destruct (icore_dropbits _ _ (RB.br_dropbits 1 b) 2 H4 eq_refl L2) as (E5 & H5).
      rewrite E5. apply step_cont_ok. split; [exact H5|].
      apply imode_stored. reflexivity.
    + destruct (RB.br_bits_of 2 (RB.br_dropbits 1 b) =? 1) eqn:T1; s5red.
      * (* fixed *)
        pose proof (icore_fixed _ _ H3) as H4.
        pose proof (icore_modez _ _ RI.M_LEN_ IS.LEN_ H4 eq_refl Hq) as H5.
        destruct (icore_dropbits _ _ (RB.br_dropbits 1 b) 2 H5 eq_refl L2) as (E6 & H6).
        rewrite E6. apply step_cont_ok. split; [exact H6|].
        apply imode_len_; [reflexivity|].
        unfold tviews_blk. cbv zeta. rewrite wbr_s. autorewrite with s5w s5i_mode.
        unfold IA.fixedtables. autorewrite with s5i_distbits s5i_distcode s5i_lenbits s5i_lencode.
        cbn [RI.q_st RI.qset_br RI.qmode RI.qset_st RI.set_mode RI.fixedtables RI.set_distbits
             RI.set_distcode RI.set_lenbits RI.set_lencode RI.s_tab RI.t_lencode RI.t_distcode].
        exact (conj (tview_lenfix _ _) (tview_distfix _ _)).
      * destruct (RB.br_bits_of 2 (RB.br_dropbits 1 b) =? 2) eqn:T2; s5red.
        -- (* dynamic *)
           pose proof (icore_modez _ _ RI.M_TABLE IS.TABLE H3 eq_refl Hq) as H4.
           destruct (icore_dropbits _ _ (RB.br_dropbits 1 b) 2 H4 eq_refl L2) as (E5 & H5).
           rewrite E5. apply step_cont_ok. split; [exact H5|].
           apply imode_table. reflexivity.
        -- (* invalid block type: BAD *)
           apply step_bad_ok. reflexivity.
  - (* last <> 0: BYTEBITS, then CHECK *)
    destruct (icore_bytebits w q _ H eq_refl) as (Eb & H1).
    s5step Eb.
    apply step_cont_ok. split.
    + exact (icore_modez _ _ RI.M_CHECK IS.CHECK H1 eq_refl Hq).
    + apply imode_check. reflexivity.
Qed.

Lemma arm_TYPE_ok : forall c w q,
  ctx_rel FL c -> inv w q -> RI.q_mode q = RI.M_TYPE ->
  step_ok (IA.arm_TYPE IS.ivar_ref FL w) (RI.inf_TYPE c q).
Proof.
  intros c w q Hc [H _] Hm.
  unfold IA.arm_TYPE, RI.inf_TYPE.
  rewrite (proj1 Hc), fl_type_s5, fl_type_rt.
  exact (arm_TYPEDO_ok c w q Hc H (or_intror Hm)).
Qed.
