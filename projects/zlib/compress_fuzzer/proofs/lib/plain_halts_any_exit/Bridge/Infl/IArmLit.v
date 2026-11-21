(** * Bridge.Infl.IArmLit — pair I10 of PAIRS.md, the output arms: LIT and MATCH.

    LIT writes one byte.  MATCH copies [min(length, left)] bytes from [offset] back in the
    output (S5: [match_copy] over its array; RT: [ob_copyn] over the closure); a copy from
    before this call's output would read the window, which is empty in the harness's call
    ([whave = 0]), so that branch only leads to BAD.

    The kit is [IArmLitKit] (moving [icore] across one write), the MATCH proof is in
    [IArmLitMatch]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmLitKit IArmLitMatch.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma arm_LIT_ok : forall w q,
  inv w q -> RI.q_mode q = RI.M_LIT ->
  step_ok (IA.arm_LIT w) (RI.inf_LIT q).
Proof.
  intros w q [H Ht] Hmode. unfold imode in Ht. rewrite Hmode in Ht.
  pose proof (icore_regs w q H) as (Hput & Hleft & _ & _ & Hp0 & Hl0 & H31 & _).
  pose proof (icore_outbuf w q H) as (Hlen & Hrel).
  pose proof (icore_cur w q H) as (EL & _ & _ & _ & _).
  rewrite Hput, Hleft in Hrel, Hlen. rewrite Hput in Hp0. rewrite Hleft in Hl0.
  rewrite Hput, Hleft in H31.
  unfold RI.inf_LIT. cbv zeta.
  unfold IA.arm_LIT. cbn [IS.abind IS.gr].
  rewrite Hleft.
  destruct (Z.eqb_spec (RI.o_left (RI.q_ob q)) 0) as [E0|E0].
  { apply step_ok_leave_ok. exact (icore_ret w q H). }
  cbn [IS.abind IS.gs IS.uc IS.ur IA.set_mode IS.us].
  apply step_ok_cont. apply inv_blk; [|left; reflexivity].
  set (o' := RI.ob_write (RI.q_ob q) (RBa.u8 (RI.u_length (RI.s_cur (RI.q_st q))))).
  set (q1 := RI.qset_ob q o').
  match goal with |- icb (IS.wset_s ?W _) _ => set (W1 := W) end.
  assert (Hc1 : icore W1 q1).
  { apply (T_outp _ _ W1 q1 H).
    all: try unfold W1; try unfold q1; s5_simpl; rt_cbn.
    all: try reflexivity.
    all: try unfold o'; cbn [RI.ob_write RI.o_buf RI.o_put RI.o_left].
    - rewrite arr_len_set. reflexivity.
    - rewrite Hput. reflexivity.
    - rewrite Hleft. apply wrap32_id. lia.
    - rewrite Hput. lia.
    - rewrite Hleft, wrap32_id by lia. lia.
    - rewrite Hput, Hleft, wrap32_id by lia. lia.
    - rewrite Hput, Hleft, wrap32_id by lia.
      replace (RI.o_put (RI.q_ob q) + 1 + (RI.o_left (RI.q_ob q) - 1))
        with (RI.o_put (RI.q_ob q) + RI.o_left (RI.q_ob q)) by lia.
      rewrite EL, k_wrap8_u8.
      apply arr_rel_set; [exact Hrel|]. intros. rewrite Hlen. lia.
    - apply zbytes_zset; [exact (icore_obytes w q H) | apply u8_byte]. }
  assert (Ht1 : tviews_blk W1 q1).
  { apply (tvb_tr _ _ _ _ Ht); try unfold W1; try unfold q1; s5_simpl; reflexivity. }
  apply B_mode; [split; assumption | | reflexivity].
  apply (icore_not_head _ _ Hc1). change (RI.q_mode q <> RI.M_HEAD). rewrite Hmode. discriminate.
Qed.

Lemma arm_MATCH_ok : forall w q,
  inv w q -> RI.q_mode q = RI.M_MATCH ->
  step_ok (IA.arm_MATCH IS.ivar_ref w) (RI.inf_MATCH q).
Proof. exact arm_MATCH_ok'. Qed.
