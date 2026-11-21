(** * Bridge.Infl.IArmLitMatch — pair I10 (helper pci-len): the MATCH arm.

    S5's [match_copy] is a [loopZ] over its output array that reads its own earlier writes;
    RT's [ob_copyn] reads the current closure.  [mc_sim] relates the two by induction on the
    copy count, from the agreement of the whole output buffer ([0, put + left)), which
    [icore] carries (written prefix in [iw_rel], zeroed tail in [icore]).  The window branch
    of MATCH needs [whave >= offset - put > 0]; the harness's call never has a window
    ([whave = 0]), so on RT's side that branch is BAD, outside [step_ok]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmLitKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateFast.

Lemma u32_id : forall z, 0 <= z < 2 ^ 32 -> RBa.u32 z = z.
Proof. intros z H. unfold RBa.u32. apply Z.mod_small. change 4294967296 with (2 ^ 32). exact H. Qed.

(** S5's copy loop body, as in [InflateArms.match_copy]. *)
Definition mc_body (win : arr) (st : arr * Z * IF.fromptr * Z) : bool * (arr * Z * IF.fromptr * Z) :=
  let '(ob, put, from, copy) := st in
  let v := match from with IF.FWin i => arr_get win i | IF.FOut i => arr_get ob i end in
  let ob := arr_set ob put v in
  let copy := wrap32 (copy - 1) in
  (negb (copy =? 0), (ob, put + 1, IF.from_succ from, copy)).

Lemma mc_eq : forall win st, IA.match_copy win st = loopZ (snd st) (mc_body win) st.
Proof. reflexivity. Qed.

Lemma ob_copyn_S : forall n win o r,
  RI.ob_copyn (S n) win o r = RI.ob_copyn n win (RI.ob_write o (RI.os_read win o r)) (RI.os_bump r).
Proof. reflexivity. Qed.

Lemma mc_loop : forall n (win : arr) rwin (ob : arr) o put i L,
  arr_len ob = L -> arr_rel ob (RI.o_buf o) 0 L -> RI.o_put o = put ->
  0 <= i < put -> put + Z.of_nat n <= L -> Z.of_nat n < 2 ^ 32 ->
  exists ob' f c, loopZ (Z.of_nat n) (mc_body win) (ob, put, IF.FOut i, Z.of_nat n)
                  = (ob', put + Z.of_nat n, f, c)
    /\ arr_len ob' = L /\ arr_rel ob' (RI.o_buf (RI.ob_copyn n rwin o (RI.OSout i))) 0 L.
Proof.
  induction n as [|n IH]; intros win rwin ob o put i L Hlen Hrel Hput Hi Hn H32.
  - exists ob, (IF.FOut i), 0. split; [|split; [exact Hlen|exact Hrel]].
    rewrite loopZ_le0 by (cbn; lia). cbn [Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - rewrite loopZ_step by lia.
    unfold mc_body at 1. cbn [IF.from_succ].
    rewrite (wrap32_id (Z.of_nat (S n) - 1)) by lia.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    assert (Hget : arr_get ob i = RI.o_buf o i) by (apply Hrel; lia).
    assert (Hrel1 : arr_rel (arr_set ob put (arr_get ob i))
                      (RI.o_buf (RI.ob_write o (RI.os_read rwin o (RI.OSout i)))) 0 L).
    { cbn [RI.ob_write RI.o_buf RI.os_read]. rewrite Hget, Hput.
      apply arr_rel_set; [exact Hrel|]. intros. rewrite Hlen. lia. }
    assert (Hlen1 : arr_len (arr_set ob put (arr_get ob i)) = L) by (rewrite arr_len_set; exact Hlen).
    rewrite ob_copyn_S.
    destruct n as [|m].
    + cbn [Z.of_nat Z.eqb negb].
      exists (arr_set ob put (arr_get ob i)), (IF.FOut (i + 1)), 0.
      split; [reflexivity|]. split; [exact Hlen1|]. exact Hrel1.
    + replace (negb (Z.of_nat (S m) =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      destruct (IH win rwin (arr_set ob put (arr_get ob i)) (RI.ob_write o (RI.os_read rwin o (RI.OSout i)))
                  (put + 1) (i + 1) L Hlen1 Hrel1)
        as (ob' & f & c & E & Hl' & Hr').
      * cbn [RI.ob_write RI.o_put]. lia.
      * lia.
      * lia.
      * lia.
      * exists ob', f, c. split; [|split; [exact Hl'|exact Hr']].
        replace (put + Z.of_nat (S (S m))) with (put + 1 + Z.of_nat (S m)) by lia.
        exact E.
Qed.

Lemma mc_sim : forall n (win : arr) rwin (ob : arr) o put i L,
  arr_len ob = L -> arr_rel ob (RI.o_buf o) 0 L -> RI.o_put o = put ->
  0 <= i < put -> put + Z.of_nat n <= L -> Z.of_nat n < 2 ^ 32 ->
  exists ob' f c, IA.match_copy win (ob, put, IF.FOut i, Z.of_nat n) = (ob', put + Z.of_nat n, f, c)
    /\ arr_len ob' = L /\ arr_rel ob' (RI.o_buf (RI.ob_copyn n rwin o (RI.OSout i))) 0 L.
Proof. intros. rewrite mc_eq. cbn [snd]. apply mc_loop; assumption. Qed.

(* ------------------------------------------------------------------------- *)
(* The arm                                                                   *)
(* ------------------------------------------------------------------------- *)

Ltac s5_simpl :=
  autorewrite with s5w s5ic_outbuf s5ir_put s5ir_left s5i_length s5i_mode.

Lemma arm_MATCH_ok' : forall w q,
  inv w q -> RI.q_mode q = RI.M_MATCH ->
  step_ok (IA.arm_MATCH IS.ivar_ref w) (RI.inf_MATCH q).
Proof.
  intros w q [H Hm] Hmode. unfold imode in Hm. rewrite Hmode in Hm.
  destruct Hm as (Ht & HL & HO).
  pose proof (icore_regs w q H) as (Hput & Hleft & _ & Hqout & Hp0 & Hl0 & H31 & Hout).
  pose proof (icore_outbuf w q H) as (Hlen & Hrel).
  pose proof (icore_cur w q H) as (EL & EO & _ & _ & _).
  pose proof (icore_win w q H) as (Hwh & Hrwh & Hsane & Hrsane).
  pose proof (icore_mode w q H) as Hmd. rewrite Hmode in Hmd.
  rewrite EL in HL. rewrite EO in HO.
  rewrite Hput, Hleft in Hrel, Hlen. rewrite Hput in Hp0. rewrite Hleft in Hl0.
  rewrite Hput, Hleft in H31.
  assert (Hqo : RI.q_out q = RI.o_put (RI.q_ob q) + RI.o_left (RI.q_ob q)) by congruence.
  unfold RI.inf_MATCH. cbv zeta.
  set (P := RI.o_put (RI.q_ob q)) in *.
  set (Lf := RI.o_left (RI.q_ob q)) in *.
  set (Len := RI.u_length (RI.s_cur (RI.q_st q))) in *.
  set (Off := RI.u_offset (RI.s_cur (RI.q_st q))) in *.
  rewrite Hqo. replace (P + Lf - Lf) with P by lia. rewrite (u32_id P) by lia.
  destruct (Z.eqb_spec Lf 0) as [E0|E0].
  { apply step_ok_leave_ok. exact (icore_ret w q H). }
  destruct (Z.ltb_spec P Off) as [EW|EW].
  { (* the window branch: whave = 0, so BAD on RT's side *)
    rewrite Hrwh, Hrsane, (u32_id (Off - P)) by lia.
    replace ((0 <? Off - P) && negb (1 =? 0)) with true by (symmetry; apply andb_true_iff; split;
      [apply Z.ltb_lt; lia | reflexivity]).
    apply step_ok_bad. reflexivity. }
  (* the copy from the output *)
  set (cw := if Lf <? Len then Lf else Len).
  assert (Hcw : 0 <= cw <= Lf /\ cw <= Len) by (unfold cw; destruct (Z.ltb_spec Lf Len); lia).
  rewrite (u32_id (Len - cw)) by lia.
  unfold IA.arm_MATCH.
  cbn [IS.abind IS.gr].
  rewrite Hleft. replace (Lf =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
  cbn [IS.abind IS.gs].
  rewrite Hout, Hput, Hleft, EO. replace (P + Lf - Lf) with P by lia. rewrite (wrap32_id P) by lia.
  replace (P <? Off) with false by (symmetry; apply Z.ltb_ge; exact EW).
  cbn [IS.abind IS.aret IS.ur IS.us].
  rewrite ?Hleft, ?EL. fold cw.
  s5_simpl. rewrite ?Hput, ?Hleft, ?EL. fold cw.
  rewrite (wrap32_id (Len - cw)) by lia.
  rewrite (wrap32_id (Lf - cw)) by lia.
  (* the copy itself *)
  assert (Hi : 0 <= P - Off < P) by lia.
  assert (Hn : P + Z.of_nat (Z.to_nat cw) <= P + Lf) by (rewrite Z2Nat.id; lia).
  assert (H32 : Z.of_nat (Z.to_nat cw) < 2 ^ 32) by (rewrite Z2Nat.id; lia).
  destruct (mc_sim (Z.to_nat cw) (IS.is_window (IS.w_s w)) (RI.w_win (RI.s_win (RI.q_st q)))
              (IS.ic_outbuf (IS.w_c w)) (RI.q_ob q) P (P - Off) (P + Lf) Hlen Hrel eq_refl Hi Hn H32)
    as (ob' & f & c & Emc & Hlen' & Hrel').
  rewrite Z2Nat.id in Emc by lia.
  rewrite IS.abind_run. cbv beta. s5_simpl. rewrite ?Hput. rewrite Emc.
  cbn [IS.abind IS.gs].
  s5_simpl. rewrite ?Hput, ?Hleft, ?EL. fold cw.
  rewrite ?(wrap32_id (Len - cw)) by lia.
  set (o' := RI.ob_copyn (Z.to_nat cw) (RI.w_win (RI.s_win (RI.q_st q))) (RI.q_ob q) (RI.OSout (P - Off))).
  assert (Hput' : RI.o_put o' = P + cw) by (unfold o'; rewrite RI.ob_copyn_put, Z2Nat.id; lia).
  assert (Hleft' : RI.o_left o' = Lf - cw) by (unfold o'; rewrite RI.ob_copyn_left, Z2Nat.id; lia).
  assert (HL0 : icore (IS.wset_s w (IS.iset_length (IS.w_s w) (Len - cw)))
                      (RI.qset_st q (RI.set_length (RI.q_st q) (Len - cw))))
    by (apply T_length; [exact H | reflexivity]).
  set (q' := RI.qset_ob (RI.qset_st q (RI.set_length (RI.q_st q) (Len - cw))) o').
  match goal with |- step_ok ((if _ then _ else _) ?W) _ => set (W3 := W) end.
  assert (Hc3 : icore W3 q').
  { apply (T_outp _ _ W3 q' HL0).
    all: try unfold W3; try unfold q'; s5_simpl; rt_cbn.
    all: try reflexivity.
    - rewrite Hlen', Hlen. reflexivity.
    - rewrite Hput'. reflexivity.
    - rewrite Hleft'. reflexivity.
    - lia.
    - lia.
    - rewrite Hput, Hleft. lia.
    - replace (P + cw + (Lf - cw)) with (P + Lf) by lia. exact Hrel'.
    - unfold o'. apply zbytes_ob_copyn; [exact (icore_wbytes w q H) | exact (icore_obytes w q H)]. }
  assert (Ht3 : tviews_blk W3 q').
  { apply (tvb_tr _ _ _ _ Ht); try unfold W3; try unfold q'; s5_simpl; reflexivity. }
  assert (Hq'm : RI.q_mode q' = RI.M_MATCH) by exact Hmode.
  destruct (Z.eqb_spec (Len - cw) 0) as [Ez|Ez].
  - cbn [IA.set_mode IS.us]. apply step_ok_cont.
    apply inv_blk; [|left; reflexivity].
    apply B_mode; [split; assumption | | reflexivity].
    apply (icore_not_head _ _ Hc3). rewrite Hq'm. discriminate.
  - cbn [IS.aret]. apply step_ok_cont.
    apply inv_match; [split; assumption | exact Hq'm | |].
    + unfold q'. rt_cbn. fold Len. lia.
    + unfold q'. rt_cbn. fold Off. lia.
Qed.
