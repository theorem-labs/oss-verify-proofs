(** * Bridge.Infl.IArmLen — pair I10 of PAIRS.md, the decode arms: LEN_, LEN, LENEXT, DIST,
    DISTEXT.

    LEN takes the fast path ([IFast.inflate_fast_sim]) when 6 input bytes and 258 output
    slots are available, otherwise decodes one literal/length ([IBits.decode1_sim] /
    [decode2_sim]) and falls through LENEXT, DIST, DISTEXT into MATCH
    ([IArmLit.arm_MATCH_ok]).

    The decode is [IArmLenDec.dseq_sim] (shared with DIST), the fallthrough arms are in
    [IArmLenExt], the state moves in [IArmLitKit]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IFast IArmLit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IArmLitKit IArmLenDec IArmLenExt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** LEN, restated with the decode as [dseq] ([reflexivity] checks the restatement). *)
Definition len_tail (here : Z) : IS.AM unit :=
  IS.abind (IS.us (fun s => IS.iset_length s (IS.code_val here))) (fun _ =>
  if IS.code_op here =? 0 then IA.set_mode IS.LIT
  else if negb (Z.land (IS.code_op here) 32 =? 0) then
    IS.abind (IA.set_back IS.ivar_ref (-1)) (fun _ => IA.set_mode IS.TYPE)
  else if negb (Z.land (IS.code_op here) 64 =? 0) then IA.go_bad MSG_invalid_literal_length_code
  else IS.abind (IS.us (fun s => IS.iset_extra s (Z.land (IS.code_op here) 15))) (fun _ =>
       IS.abind (IA.set_mode IS.LENEXT) (fun _ => IA.arm_LENEXT IS.ivar_ref))).

Definition len_fast : IS.AM unit :=
  IS.abind (IS.amodify (fun w => IS.LOAD (IF.inflate_fast (IS.RESTORE w)))) (fun _ =>
  IS.abind (IS.gs (fun s => s)) (fun s =>
  if IS.is_mode s =? IS.TYPE then IA.set_back IS.ivar_ref (-1) else IS.aret tt)).

Lemma arm_LEN_eq : forall w, IA.arm_LEN IS.ivar_ref w =
  IS.abind (IS.gr (fun r => r)) (fun r =>
    if IS.iv_fast IS.ivar_ref && (6 <=? IS.ir_have r) && (258 <=? IS.ir_left r) && (IS.ir_bits r <? 8)
    then len_fast
    else IS.abind (IA.set_back IS.ivar_ref 0) (fun _ =>
         IS.abind (IS.gs (fun s => s)) (fun s => dseq (IS.is_lencode s) (IS.is_lenbits s) KLens len_tail))) w.
Proof. reflexivity. Qed.

Lemma abind_setback : forall {B} v (g : unit -> IS.AM B) w,
  IS.abind (IA.set_back IS.ivar_ref v) g w = g tt (IS.wset_s w (IS.iset_back (IS.w_s w) v)).
Proof. reflexivity. Qed.

Lemma set_back_eq : forall v w,
  IA.set_back IS.ivar_ref v w = IS.ARun tt (IS.wset_s w (IS.iset_back (IS.w_s w) v)).
Proof. reflexivity. Qed.

(** RT's LEN with the fast-path guard false: the slow branch, verbatim. *)
Lemma inf_LEN_slow : forall q,
  (6 <=? RB.br_have (RI.q_br q)) && (258 <=? RI.o_left (RI.q_ob q)) = false ->
  RI.inf_LEN q =
  match RI.inf_decode RI.sub_len (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q))))
          (RI.t_lenbits (RI.s_tab (RI.q_st q))) (RI.q_br q) with
  | RI.DecFuel => RI.InfFuel
  | RI.DecLeave b' => RI.InfLeave (RI.qset_br (RI.qset_st q (RI.set_back (RI.q_st q) 0)) b')
  | RI.DecOk h b' nb =>
      let q0 := RI.qset_st q (RI.set_back (RI.q_st q) 0) in
      let q1 := RI.qset_br (RI.qset_st q0 (RI.set_length (RI.set_back (RI.q_st q0) (0 + nb)) (RBa.c_val h))) b' in
      if RBa.c_op h =? 0 then RI.InfCont (RI.qmode q1 RI.M_LIT)
      else if negb (Z.land (RBa.c_op h) 32 =? 0) then
        RI.InfCont (RI.qmode (RI.qset_st q1 (RI.set_back (RI.q_st q1) (-1))) RI.M_TYPE)
      else if negb (Z.land (RBa.c_op h) 64 =? 0) then RI.InfCont (RI.qbad q1 RIF.MSG_LIT_LEN_CODE)
      else RI.inf_LENEXT (RI.qmode (RI.qset_st q1 (RI.set_extra (RI.q_st q1) (Z.land (RBa.c_op h) 15))) RI.M_LENEXT)
  end.
Proof. intros q G. unfold RI.inf_LEN. cbv zeta. rewrite G. reflexivity. Qed.

(** zlib 1.4: RT14's LEN with 1.4's gate false: the same slow branch. *)
Lemma inf_LEN14_slow : forall q,
  (6 <=? RB.br_have (RI.q_br q)) && (258 <=? RI.o_left (RI.q_ob q)) && (RB.br_bits (RI.q_br q) <? 8) = false ->
  RI14.inf_LEN14 q =
  match RI.inf_decode RI.sub_len (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q))))
          (RI.t_lenbits (RI.s_tab (RI.q_st q))) (RI.q_br q) with
  | RI.DecFuel => RI.InfFuel
  | RI.DecLeave b' => RI.InfLeave (RI.qset_br (RI.qset_st q (RI.set_back (RI.q_st q) 0)) b')
  | RI.DecOk h b' nb =>
      let q0 := RI.qset_st q (RI.set_back (RI.q_st q) 0) in
      let q1 := RI.qset_br (RI.qset_st q0 (RI.set_length (RI.set_back (RI.q_st q0) (0 + nb)) (RBa.c_val h))) b' in
      if RBa.c_op h =? 0 then RI.InfCont (RI.qmode q1 RI.M_LIT)
      else if negb (Z.land (RBa.c_op h) 32 =? 0) then
        RI.InfCont (RI.qmode (RI.qset_st q1 (RI.set_back (RI.q_st q1) (-1))) RI.M_TYPE)
      else if negb (Z.land (RBa.c_op h) 64 =? 0) then RI.InfCont (RI.qbad q1 RIF.MSG_LIT_LEN_CODE)
      else RI.inf_LENEXT (RI.qmode (RI.qset_st q1 (RI.set_extra (RI.q_st q1) (Z.land (RBa.c_op h) 15))) RI.M_LENEXT)
  end.
Proof. intros q G. unfold RI14.inf_LEN14. cbv zeta. rewrite G. reflexivity. Qed.

(** zlib 1.4: RT14's LEN on 1.4's fast path is RT's ([Inflate14.inf_LEN14_low]). *)
Lemma inf_LEN14_fast : forall q,
  6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) -> RB.br_bits (RI.q_br q) < 8 ->
  RI14.inf_LEN14 q = match RIF.if_model (fast_args q) with
                     | None => RI.InfFuel
                     | Some y => RI.InfCont (fast_res (fast_q5 q y))
                     end.
Proof. intros q H6 H258 Hb. rewrite (RI14.inf_LEN14_low q Hb). exact (inf_LEN_fast q H6 H258). Qed.

Lemma q5_mode : forall q y, RI.q_mode (fast_q5 q y) =
  match RIF.y_exit y with RIF.ExLen => RI.q_mode q | RIF.ExType => RI.M_TYPE | RIF.ExBad _ => RI.M_BAD end.
Proof. intros q y. unfold fast_q5. destruct (RIF.y_exit y); reflexivity. Qed.

Lemma fast_res_notype : forall q5, RI.q_mode q5 <> RI.M_TYPE -> fast_res q5 = q5.
Proof. intros q5 H. unfold fast_res. destruct (RI.q_mode q5); try reflexivity. contradiction. Qed.

Lemma fast_res_type : forall q5, RI.q_mode q5 = RI.M_TYPE ->
  fast_res q5 = RI.qset_st q5 (RI.set_back (RI.q_st q5) (-1)).
Proof. intros q5 H. unfold fast_res. rewrite H. reflexivity. Qed.

Lemma tent_len : forall h, code_rng h -> tent KLens (RBa.code_enc h) -> tsub KLens (RBa.c_op h) = false ->
  RBa.c_op h <> 0 -> Z.land (RBa.c_op h) 64 = 0 ->
  0 <= Z.land (RBa.c_op h) 15 <= 5 /\ RBa.c_val h + 2 ^ Z.land (RBa.c_op h) 15 <= 259.
Proof.
  intros h Hr Ht Hs H0 H64. unfold tent in Ht. cbv zeta iota beta in Ht.
  rewrite (enc_op _ Hr), (enc_val _ Hr) in Ht.
  destruct Ht as (H16 & Hl).
  unfold tsub in Hs. apply andb_false_iff in Hs.
  assert (H240 : Z.land (RBa.c_op h) 240 <> 0).
  { destruct Hs as [Hs|Hs].
    - apply negb_false_iff, Z.eqb_eq in Hs. contradiction.
    - apply Z.eqb_neq in Hs. exact Hs. }
  destruct (Z.eq_dec (Z.land (RBa.c_op h) 16) 0) as [E|E].
  - exfalso. apply H240. apply Hl; assumption.
  - destruct (H16 E) as (A & B). split; [|exact B]. split; [apply Z.land_nonneg; lia | exact A].
Qed.

Lemma arm_LEN_ok : forall w q,
  inv w q -> RI.q_mode q = RI.M_LEN ->
  step_ok (IA.arm_LEN IS.ivar_ref w) (RI14.inf_LEN14 q).
Proof.
  intros w q [H Ht] Hmode. unfold imode in Ht. rewrite Hmode in Ht.
  assert (Hb : icb w q) by (split; assumption).
  assert (Hnh : RI.q_mode q <> RI.M_HEAD) by (rewrite Hmode; discriminate).
  pose proof (icore_regs w q H) as (Hput & Hleft & Hhave & _ & Hp0 & Hl0 & H31 & _).
  rewrite arm_LEN_eq. cbn [IS.abind IS.gr].
  pose proof (icore_brel _ _ H) as (_ & Hbits & _).
  rewrite Hhave, Hleft, Hbits. cbn [IS.iv_fast IS.ivar_ref andb].
  destruct ((6 <=? RB.br_have (RI.q_br q)) && (258 <=? RI.o_left (RI.q_ob q)) && (RB.br_bits (RI.q_br q) <? 8)) eqn:G.
  - (* the fast path (zlib 1.4: bits < 8 too) *)
    apply andb_true_iff in G. destruct G as [G Gb8]. apply Z.ltb_lt in Gb8.
    apply andb_true_iff in G. destruct G as [G6 G258]. apply Z.leb_le in G6, G258.
    rewrite (inf_LEN14_fast q G6 G258 Gb8).
    destruct (RIF.if_model (fast_args q)) as [y|] eqn:Ey; [|exact I].
    destruct (RIF.y_exit y) as [| |m] eqn:Ex.
    3: { apply step_ok_bad. rewrite fast_res_notype by (rewrite q5_mode, Ex; discriminate).
         rewrite q5_mode, Ex. reflexivity. }
    all: assert (Hnb : forall m, RIF.y_exit y <> RIF.ExBad m) by (intros m; rewrite Ex; discriminate).
    all: destruct (inflate_fast_sim w q y H Ht Hmode G6 G258 Ey Hnb) as [Hc5 Ht5].
    all: unfold len_fast; cbn [IS.abind IS.amodify IS.gs].
    all: revert Hc5 Ht5; generalize (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) as W5; intros W5 Hc5 Ht5.
    all: pose proof (q5_mode q y) as Hm5; rewrite Ex in Hm5.
    all: rewrite (icore_mode _ _ Hc5), Hm5.
    + (* back in LEN *)
      rewrite Hmode. replace (RI.m_val RI.M_LEN =? IS.TYPE) with false by reflexivity.
      cbn [IS.aret]. rewrite fast_res_notype by (rewrite Hm5, Hmode; discriminate).
      apply step_ok_cont. apply inv_blk; [split; assumption | left; rewrite Hm5; exact Hmode].
    + (* end of block: TYPE *)
      replace (RI.m_val RI.M_TYPE =? IS.TYPE) with true by reflexivity.
      rewrite set_back_eq, (fast_res_type _ Hm5).
      apply step_ok_cont. apply inv_type; [|exact Hm5].
      apply T_back; [exact Hc5 | reflexivity].
  - (* the slow path *)
    rewrite (inf_LEN14_slow q G). cbv zeta.
    pose proof (icore_tab w q H) as (Hlb & _).
    rewrite abind_setback. cbv beta. cbn [IS.abind IS.gs].
    autorewrite with s5w s5i_back.
    destruct (RI.inf_decode RI.sub_len (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q))))
                (RI.t_lenbits (RI.s_tab (RI.q_st q))) (RI.q_br q)) as [h b' nb|b'|] eqn:Ed.
    3: { exact I. }
    2: { apply step_ok_leave_ok. exact (icore_ret w q H). }
    rewrite <- Hlb in Ed.
    assert (Hcb0 : icb (IS.wset_s w (IS.iset_back (IS.w_s w) 0)) (RI.qset_st q (RI.set_back (RI.q_st q) 0)))
      by (apply B_back; [exact Hb | reflexivity]).
    assert (Htv : tview (IS.code_at (IS.w_s (IS.wset_s w (IS.iset_back (IS.w_s w) 0))) (IS.is_lencode (IS.w_s w)))
                        (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q))))
                        (IS.is_lenbits (IS.w_s w)) KLens).
    { rewrite (code_at_codes (IS.w_s w)) by (autorewrite with s5w s5i_back; reflexivity).
      exact (proj1 Ht). }
    destruct (dseq_sim KLens (IS.is_lencode (IS.w_s w)) (IS.is_lenbits (IS.w_s w))
                (RI.tbl_of (RI.q_st q) (RI.t_lencode (RI.s_tab (RI.q_st q)))) len_tail
                (IS.wset_s w (IS.iset_back (IS.w_s w) 0)) (RI.qset_st q (RI.set_back (RI.q_st q) 0))
                h b' nb Hcb0 Htv Ed)
      as (W1 & E1 & Hc1 & Hr & Hte & Hts).
    rewrite E1. unfold len_tail.
    rewrite abind_us. cbv beta.
    rewrite (enc_op _ Hr), (enc_val _ Hr).
    pose proof (B_length _ _ (RBa.c_val h) (RBa.c_val h) Hc1 eq_refl) as Hc2.
    match type of Hc2 with icb ?W ?Q => set (W2 := W) in *; set (Q2 := Q) in * end.
    assert (Hnh2 : IS.is_mode (IS.w_s W2) <> IS.HEAD) by (apply (icore_not_head _ _ (proj1 Hc2)); exact Hnh).
    destruct (Z.eqb_spec (RBa.c_op h) 0) as [Eop|Eop].
    { (* a literal *)
      cbn [IA.set_mode IS.us]. apply step_ok_cont.
      apply inv_blk; [|right; left; reflexivity].
      apply B_mode; [exact Hc2 | exact Hnh2 | reflexivity]. }
    destruct (Z.eqb_spec (Z.land (RBa.c_op h) 32) 0) as [E32|E32].
    2: { (* end of block *)
      cbn [negb]. rewrite abind_setback. cbv beta. cbn [IA.set_mode IS.us].
      apply step_ok_cont. apply inv_type; [|reflexivity].
      apply T_mode; [| | reflexivity].
      - apply T_back; [exact (proj1 Hc2) | reflexivity].
      - autorewrite with s5w s5i_back. exact Hnh2. }
    destruct (Z.eqb_spec (Z.land (RBa.c_op h) 64) 0) as [E64|E64].
    2: { cbn [negb]. apply step_ok_bad. reflexivity. }
    (* a length: LENEXT *)
    cbn [negb]. rewrite abind_us. cbv beta. cbn [IS.abind IA.set_mode IS.us].
    pose proof (B_extra _ _ (Z.land (RBa.c_op h) 15) (Z.land (RBa.c_op h) 15) Hc2 eq_refl) as Hc3.
    destruct (tent_len h Hr Hte Hts Eop E64) as (HE & HL).
    pose proof Hr as (_ & _ & Hval).
    apply arm_LENEXT_ok'; [| reflexivity | | |].
    + apply B_mode; [exact Hc3 | | reflexivity].
      autorewrite with s5w s5i_extra. exact Hnh2.
    + rt_cbn. exact HE.
    + rt_cbn. lia.
    + rt_cbn. exact HL.
Qed.

Lemma arm_LEN__ok : forall w q,
  inv w q -> RI.q_mode q = RI.M_LEN_ ->
  step_ok (IA.arm_LEN_ IS.ivar_ref w) (RI14.inf_LEN_14 q).
Proof.
  intros w q [H Ht] Hmode. unfold imode in Ht. rewrite Hmode in Ht.
  unfold IA.arm_LEN_, RI14.inf_LEN_14. cbn [IS.abind IA.set_mode IS.us].
  apply arm_LEN_ok; [|reflexivity].
  apply inv_blk; [|left; reflexivity].
  apply B_mode; [split; assumption | | reflexivity].
  apply (icore_not_head _ _ H). rewrite Hmode. discriminate.
Qed.
