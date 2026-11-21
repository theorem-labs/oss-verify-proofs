(** * Bridge.Infl.IArmStored — pair I8 of PAIRS.md: STORED, COPY_ and COPY.

    STORED byte-aligns, reads LEN/NLEN and falls through to COPY_ then COPY.  COPY moves
    [min(length, have, left)] bytes straight from the input to the output (S5: [arr_blit]
    on its arrays; RT: [zcopy] on closures), and sets TYPE once [length] is 0. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmTypeKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* COPY, evaluated                                                           *)
(* ------------------------------------------------------------------------- *)

(** [copy = min(length, have, left)] as both arms compute it. *)
Definition copy_amt (have left len : Z) : Z :=
  let c1 := if have <? len then have else len in
  if left <? c1 then left else c1.

Lemma copy_amt_bounds : forall have left len, 0 <= have -> 0 <= left -> 0 <= len ->
  0 <= copy_amt have left len /\ copy_amt have left len <= have
  /\ copy_amt have left len <= left /\ copy_amt have left len <= len.
Proof.
  intros have left len H1 H2 H3. unfold copy_amt. cbv zeta.
  destruct (Z.ltb_spec have len); destruct (Z.ltb_spec left have); destruct (Z.ltb_spec left len);
    lia.
Qed.

(** S5's state after a copy of [cp] bytes. *)
Definition copy_w (w : IS.iw) (cp : Z) : IS.iw :=
  let s := IS.w_s w in let r := IS.w_r w in let c := IS.w_c w in
  IS.wset_s
    (IS.wset_r
       (IS.wset_c w (IS.icset_outbuf c (arr_blit (IS.ic_outbuf c) (IS.ir_put r) (IS.ic_input c)
                                                 (IS.ir_next r) cp)))
       (IS.irset_put (IS.irset_left (IS.irset_next (IS.irset_have r (wrap32 (IS.ir_have r - cp)))
                                                   (IS.ir_next r + cp))
                                    (wrap32 (IS.ir_left r - cp)))
                     (IS.ir_put r + cp)))
    (IS.iset_length s (wrap32 (IS.is_length s - cp))).

(** RT's. *)
Definition copy_q (q : RI.InfSt) (cp : Z) : RI.InfSt :=
  let st := RI.q_st q in let b := RI.q_br q in let o := RI.q_ob q in
  RI.qset_ob
    (RI.qset_br (RI.qset_st q (RI.set_length st (RBa.u32 (RI.u_length (RI.s_cur st) - cp))))
                (RB.mkBR (RB.br_in b) (RB.br_have b - cp) (RB.br_next b + cp) (RB.br_hold b)
                         (RB.br_bits b)))
    (RI.mkOB (RI.zcopy (Z.to_nat cp) (RI.o_buf o) (RI.o_put o) (RB.br_in b) (RB.br_next b))
             (RI.o_put o + cp) (RI.o_left o - cp)).

Lemma arm_COPY_eval : forall w, IA.arm_COPY w =
  if negb (IS.is_length (IS.w_s w) =? 0) then
    let cp := copy_amt (IS.ir_have (IS.w_r w)) (IS.ir_left (IS.w_r w)) (IS.is_length (IS.w_s w)) in
    if cp =? 0 then IS.ALeave w else IS.ARun tt (copy_w w cp)
  else IS.ARun tt (IS.wset_s w (IS.iset_mode (IS.w_s w) IS.TYPE)).
Proof.
  intros w. unfold IA.arm_COPY, IS.abind, IS.gs, IS.gr. cbv zeta.
  destruct (negb (IS.is_length (IS.w_s w) =? 0)); [|reflexivity].
  unfold copy_amt. cbv zeta.
  destruct (_ =? 0); reflexivity.
Qed.

Lemma inf_COPY_eval : forall q, RI.inf_COPY q =
  if RI.u_length (RI.s_cur (RI.q_st q)) =? 0 then RI.InfCont (RI.qmode q RI.M_TYPE)
  else
    let cp := copy_amt (RB.br_have (RI.q_br q)) (RI.o_left (RI.q_ob q))
                       (RI.u_length (RI.s_cur (RI.q_st q))) in
    if cp =? 0 then RI.InfLeave q else RI.InfCont (copy_q q cp).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* The copy keeps icore                                                      *)
(* ------------------------------------------------------------------------- *)

(** [arr_blit] against [zcopy] on the whole live output range [[0, put + left)]. *)
Lemma blit_zcopy : forall ob obuf put left inp brin nx cp,
  arr_len ob = put + left -> 0 <= put -> 0 <= cp <= left -> 0 <= nx ->
  arr_rel ob obuf 0 put -> arr_rel ob obuf put (put + left) ->
  (forall i, 0 <= i -> arr_get inp i = brin i) ->
  arr_rel (arr_blit ob put inp nx cp) (RI.zcopy (Z.to_nat cp) obuf put brin nx) 0 (put + left).
Proof.
  intros ob obuf put left inp brin nx cp Hl Hp Hc Hn H1 H2 Hi j Hj.
  rewrite arr_get_blit.
  assert (Hinb : arr_inb ob j = true) by (apply arr_inb_spec; lia).
  rewrite Hinb, andb_true_r.
  destruct (Z.leb_spec put j) as [L1|L1]; destruct (Z.ltb_spec j (put + Z.max 0 cp)) as [L2|L2];
    cbn [andb].
  - assert (E : RI.zcopy (Z.to_nat cp) obuf put brin nx (put + Z.of_nat (Z.to_nat (j - put)))
                = brin (nx + Z.of_nat (Z.to_nat (j - put)))) by (apply RI.zcopy_hit; lia).
    rewrite Z2Nat.id in E by lia.
    replace (put + (j - put)) with j in E by lia.
    rewrite E, Hi by lia. reflexivity.
  - rewrite RI.zcopy_miss by (intros m Hm; lia). apply H2; lia.
  - rewrite RI.zcopy_miss by (intros m Hm; lia). apply H1; lia.
  - rewrite RI.zcopy_miss by (intros m Hm; lia). apply H1; lia.
Qed.

Lemma blit_rel2 : forall ob obuf put left inp brin nx cp,
  arr_len ob = put + left -> 0 <= put -> 0 <= cp <= left -> 0 <= nx ->
  arr_rel ob obuf 0 put -> arr_rel ob obuf put (put + left) ->
  (forall i, 0 <= i -> arr_get inp i = brin i) ->
  arr_rel (arr_blit ob put inp nx cp) (RI.zcopy (Z.to_nat cp) obuf put brin nx) 0 (put + cp)
  /\ arr_rel (arr_blit ob put inp nx cp) (RI.zcopy (Z.to_nat cp) obuf put brin nx)
             (put + cp) (put + cp + (left - cp)).
Proof.
  intros ob obuf put left inp brin nx cp Hl Hp Hc Hn H1 H2 Hi.
  pose proof (blit_zcopy ob obuf put left inp brin nx cp Hl Hp Hc Hn H1 H2 Hi) as Hb.
  split; apply (arr_rel_narrow _ _ 0 (put + left)); try lia; exact Hb.
Qed.

Lemma icore_copy : forall w q cp,
  icore w q -> 0 < cp ->
  cp <= IS.is_length (IS.w_s w) -> cp <= IS.ir_have (IS.w_r w) -> cp <= IS.ir_left (IS.w_r w) ->
  icore (copy_w w cp) (copy_q q cp).
Proof.
  intros w q cp H Hc0 Hcl Hch Hcf.
  pose proof (icore_length_eq w q H) as El.
  pose proof (icore_core w q H) as Hcr.
  icore_destr H.
  assert (Ehv : wrap32 (IS.ir_have (IS.w_r w) - cp) = IS.ir_have (IS.w_r w) - cp)
    by (apply wrap32_id; lia).
  assert (Elf : wrap32 (IS.ir_left (IS.w_r w) - cp) = IS.ir_left (IS.w_r w) - cp)
    by (apply wrap32_id; lia).
  assert (Ecr : ist_core_rel (IS.iset_length (IS.w_s w) (wrap32 (IS.is_length (IS.w_s w) - cp)))
                  (RI.set_length (RI.q_st q) (RBa.u32 (RI.u_length (RI.s_cur (RI.q_st q)) - cp))))
    by (rewrite <- El, <- wrap32_u32; exact (icr_length _ _ _ Hcr)).
  assert (Hcd : forall i, code_rng (RI.t_codes (RI.s_tab (RI.set_length (RI.q_st q)
                  (RBa.u32 (RI.u_length (RI.s_cur (RI.q_st q)) - cp)))) i))
    by exact Hcodes.
  pose proof (blit_rel2 (IS.ic_outbuf (IS.w_c w)) (RI.o_buf (RI.q_ob q)) (IS.ir_put (IS.w_r w))
                (IS.ir_left (IS.w_r w)) (IS.ic_input (IS.w_c w)) (RB.br_in (RI.q_br q))
                (IS.ir_next (IS.w_r w)) cp Hol Hp0 ltac:(lia) Hn0 Hor Hot
                (fun i Hi => proj1 (Hin i Hi))) as [Hb1 Hb2].
  assert (Hz' : forall v, zstrm_rel (IS.icset_outbuf (IS.w_c w) v) (RI.q_z q))
    by (intros v; unfold zstrm_rel in *; autorewrite with s5ic_outbuf; exact Hz).
  unfold copy_w, copy_q, icore, iw_rel. cbv zeta.
  autorewrite with s5w s5ic_outbuf s5ir_put s5ir_left s5ir_next s5ir_have s5i_length.
  cbn [RI.qset_ob RI.qset_br RI.qset_st RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret
       RB.br_in RB.br_have RB.br_next RB.br_hold RB.br_bits RI.o_buf RI.o_put RI.o_left].
  rewrite Ehv, Elf, arr_len_blit, <- Hput, <- Hn, <- Hv, <- Hleft, <- Hh, <- Hbt.
  assert (Hzb : zbytes (RI.zcopy (Z.to_nat cp) (RI.o_buf (RI.q_ob q)) (IS.ir_put (IS.w_r w))
                           (RB.br_in (RI.q_br q)) (IS.ir_next (IS.w_r w)))).
  { apply zbytes_zcopy; [exact Hobyte|]. intros i Hi0. apply (Hin i). lia. }
  unfold zbytes in Hzb.
  csplit; try apply Hz'; try reflexivity; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The three arms                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma arm_COPY_ok : forall w q,
  icore w q -> RI.q_mode q = RI.M_COPY -> 0 <= IS.is_length (IS.w_s w) < 65536 ->
  step_ok (IA.arm_COPY w) (RI.inf_COPY q).
Proof.
  intros w q H Hm Hlen.
  assert (Hq : RI.q_mode q <> RI.M_HEAD) by (rewrite Hm; discriminate).
  pose proof (icore_length_eq w q H) as El.
  pose proof H as H'. icore_destr H'.
  rewrite arm_COPY_eval, inf_COPY_eval. cbv zeta.
  assert (E0 : (RI.u_length (RI.s_cur (RI.q_st q)) =? 0) = (IS.is_length (IS.w_s w) =? 0))
    by (rewrite El; reflexivity).
  rewrite E0.
  destruct (IS.is_length (IS.w_s w) =? 0) eqn:EZ; cbn [negb].
  - (* length = 0: TYPE *)
    apply step_cont_ok. split.
    + exact (icore_modez _ _ RI.M_TYPE IS.TYPE H eq_refl Hq).
    + apply imode_type. reflexivity.
  - assert (Ecp : copy_amt (RB.br_have (RI.q_br q)) (RI.o_left (RI.q_ob q))
                           (RI.u_length (RI.s_cur (RI.q_st q)))
                  = copy_amt (IS.ir_have (IS.w_r w)) (IS.ir_left (IS.w_r w)) (IS.is_length (IS.w_s w)))
      by (rewrite <- Hv, <- Hleft, <- El; reflexivity).
    rewrite Ecp.
    pose proof (copy_amt_bounds (IS.ir_have (IS.w_r w)) (IS.ir_left (IS.w_r w))
                  (IS.is_length (IS.w_s w)) Hv0 Hl0 (proj1 Hlen)) as Hcb.
    set (cp := copy_amt (IS.ir_have (IS.w_r w)) (IS.ir_left (IS.w_r w)) (IS.is_length (IS.w_s w)))
      in *.
    destruct (cp =? 0) eqn:E2.
    + (* nothing to copy: a leave with Z_OK *)
      apply step_leave_ok. exact Hret.
    + apply Z.eqb_neq in E2.
      apply step_cont_ok. split.
      * apply icore_copy; [exact H | lia | lia | lia | lia].
      * apply imode_copy; [exact Hm|].
        unfold copy_w. cbv zeta. autorewrite with s5w s5i_length.
        rewrite wrap32_id by lia. lia.
Qed.

Lemma arm_COPY__ok : forall w q,
  icore w q -> RI.q_mode q = RI.M_COPY_ -> 0 <= IS.is_length (IS.w_s w) < 65536 ->
  step_ok (IA.arm_COPY_ w) (RI.inf_COPY_ q).
Proof.
  intros w q H Hm Hlen.
  assert (Hq : RI.q_mode q <> RI.M_HEAD) by (rewrite Hm; discriminate).
  unfold IA.arm_COPY_, RI.inf_COPY_. s5red.
  apply arm_COPY_ok.
  - exact (icore_modez _ _ RI.M_COPY IS.COPY H eq_refl Hq).
  - reflexivity.
  - autorewrite with s5w s5i_mode. exact Hlen.
Qed.

Lemma arm_STORED_ok : forall c w q,
  ctx_rel FL c -> inv w q -> RI.q_mode q = RI.M_STORED ->
  step_ok (IA.arm_STORED IS.ivar_ref FL w) (RI.inf_STORED c q).
Proof.
  intros c w q [Hfl _] [H _] Hm.
  assert (Hq : RI.q_mode q <> RI.M_HEAD) by (rewrite Hm; discriminate).
  unfold IA.arm_STORED, RI.inf_STORED. cbv zeta.
  rewrite Hfl, fl_trees_s5, fl_trees_rt.
  destruct (icore_bytebits w q _ H eq_refl) as (Eb & H1).
  s5step Eb.
  destruct (RI.inf_nb 32 (RB.br_bytebits (RI.q_br q))) as [b|b] eqn:Enb.
  2: { apply step_leave_ok. exact (icore_ret w q H). }
  destruct (icore_needbits _ _ (RB.br_bytebits (RI.q_br q)) b 32 H1 eq_refl ltac:(lia) Enb)
    as (E2 & H2 & L2).
  s5step E2.
  s5step (icore_hold _ _ b H2 eq_refl).
  destruct (negb (Z.land (RB.br_hold b) 65535 =? Z.lxor (Z.shiftr (RB.br_hold b) 16) 65535)) eqn:EB;
    s5red.
  - (* LEN/NLEN mismatch: BAD *)
    apply step_bad_ok. reflexivity.
  - rewrite (wrap32_u32 (RB.br_hold b)).
    pose proof (icore_length _ _ (Z.land (RBa.u32 (RB.br_hold b)) 65535) H2) as H3.
    destruct (icore_initbits _ _ b H3 eq_refl) as (Ei & H4).
    s5step Ei.
    pose proof (icore_modez _ _ RI.M_COPY_ IS.COPY_ H4 eq_refl Hq) as H5.
    apply arm_COPY__ok; [exact H5 | reflexivity |].
    rewrite wbr_s. autorewrite with s5w s5i_mode s5i_length.
    exact (wrap16_range _).
Qed.
