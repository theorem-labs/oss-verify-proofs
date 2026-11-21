(** * Bridge.Infl.IFast — pair I16 of PAIRS.md: [inflate_fast], S5 vs RT.

    LEN's fast path ([inflate.c:1026-1033]) is RESTORE, [inflate_fast], LOAD on both
    sides.  [fast_args]/[fast_q5]/[fast_res] are RT's call and its write-back, verbatim
    from [Inflate.inf_LEN] ([inf_LEN_fast] checks that by [reflexivity]).

    S5's decode chains have fuel 4 and silently stop at 0; RT's have 16 and fail.  Under
    [tview] a chain is at most two deep, so neither runs out.  S5's trip fuel
    ([8 * avail_in + avail_out + 80]) is at least RT's ([avail_out - 256]), so the lockstep
    ([IFastLoop.fl_loop]) needs no fuel lemma.  The window branch only ever leads to BAD in
    the harness's call ([whave = 0]); BAD exits are outside [step_ok].

    [inflate_fast_sim_x] is the main proof, with two hypotheses spelled out:
    [ir_bits <= 8 * ir_next] and the [xviews_blk] table facts (extra bits at most 5 / 13;
    every entry the fast path chains on is a [tsub] link), both carried to the post-state.
    The statement is false without them (counterexamples in pci-fast's NEEDS.md); IInv now
    has both ([icore]'s bits conjunct, [tent]), so the published [inflate_fast_sim] is a
    corollary. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IFastKit IFastTrip IFastLoop IFastBytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateFast.
Module RIF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.InflateFast.

Definition fast_args (q : RI.InfSt) : RIF.IfArgs :=
  let st := RI.q_st q in let tb := RI.s_tab st in let b := RI.q_br q in let o := RI.q_ob q in
  let q0 := RI.q_restore q in
  {| RIF.a_inbuf     := RB.br_in b;
     RIF.a_next_in   := RB.br_next b;
     RIF.a_avail_in  := RB.br_have b;
     RIF.a_buf       := RI.o_buf o;
     RIF.a_next_out  := RI.o_put o;
     RIF.a_avail_out := RI.o_left o;
     RIF.a_start     := RI.q_out q;
     RIF.a_wsize     := RI.w_wsize (RI.s_win st);
     RIF.a_whave     := RI.w_whave (RI.s_win st);
     RIF.a_wnext     := RI.w_wnext (RI.s_win st);
     RIF.a_window    := RI.w_win (RI.s_win st);
     RIF.a_lcode     := RI.tbl_of st (RI.t_lencode tb);
     RIF.a_dcode     := RI.tbl_of st (RI.t_distcode tb);
     RIF.a_lenbits   := RI.t_lenbits tb;
     RIF.a_distbits  := RI.t_distbits tb;
     RIF.a_sane      := RI.t_sane tb;
     RIF.a_hold      := RI.s_hold (RI.q_st q0);
     RIF.a_bits      := RI.s_bits (RI.q_st q0) |}.

Definition fast_q5 (q : RI.InfSt) (y : RIF.IfOut) : RI.InfSt :=
  let b := RI.q_br q in
  let q0 := RI.q_restore q in
  let st1 := RI.set_bits (RI.set_hold (RI.q_st q0) (RIF.y_hold y)) (RIF.y_bits y) in
  let q1  := RI.qset_st q0 st1 in
  let q2  := RI.qset_br q1 {| RB.br_in := RB.br_in b; RB.br_have := RIF.y_avail_in y;
                              RB.br_next := RIF.y_in y;
                              RB.br_hold := RB.br_hold b; RB.br_bits := RB.br_bits b |} in
  let q3  := RI.qset_ob q2 {| RI.o_buf := RIF.y_buf y; RI.o_put := RIF.y_out y;
                              RI.o_left := RIF.y_avail_out y |} in
  let q4  := match RIF.y_exit y with
             | RIF.ExLen    => q3
             | RIF.ExType   => RI.qmode q3 RI.M_TYPE
             | RIF.ExBad m  => RI.qbad q3 m
             end in
  RI.q_load q4.

Definition fast_res (q5 : RI.InfSt) : RI.InfSt :=
  match RI.q_mode q5 with
  | RI.M_TYPE => RI.qset_st q5 (RI.set_back (RI.q_st q5) (-1))
  | _ => q5
  end.

Lemma inf_LEN_fast : forall q,
  6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) ->
  RI.inf_LEN q = match RIF.if_model (fast_args q) with
                 | None => RI.InfFuel
                 | Some y => RI.InfCont (fast_res (fast_q5 q y))
                 end.
Proof.
  intros q H6 H258. unfold RI.inf_LEN.
  rewrite (proj2 (Z.leb_le 6 _) H6), (proj2 (Z.leb_le 258 _) H258). cbn [andb].
  reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* S5's [inflate_fast], cut at its loop                                      *)
(* ------------------------------------------------------------------------- *)

(** The loop context, start state, fuel and epilogue of S5's [inflate_fast], verbatim. *)
Definition fx (w : IS.iw) : IF.ffx :=
  let s := IS.w_s w in let c := IS.w_c w in let r := IS.w_r w in
  let in_ := IS.ic_next_in c in
  let last := in_ + wrap32 (IS.ic_avail_in c - 5) in
  let out := IS.ic_next_out c in
  let beg := out - wrap32 (IS.ir_out r - IS.ic_avail_out c) in
  let end_ := out + wrap32 (IS.ic_avail_out c - 257) in
  IF.mkFX (IS.ic_input c) last beg end_ (IS.is_wsize s) (IS.is_whave s) (IS.is_wnext s) (IS.is_window s)
          (IF.zmask (IS.is_lenbits s)) (IF.zmask (IS.is_distbits s)) (IS.is_sane s).

Definition ff0 (w : IS.iw) : IF.ffs :=
  IF.mkF (IS.ic_next_in (IS.w_c w)) (IS.ic_next_out (IS.w_c w)) (IS.is_hold (IS.w_s w)) (IS.is_bits (IS.w_s w))
         0 0 0 (IF.FOut 0) (IS.ic_outbuf (IS.w_c w)).

Definition ffuel (w : IS.iw) : Z := 8 * IS.ic_avail_in (IS.w_c w) + IS.ic_avail_out (IS.w_c w) + 80.

Definition fepi (w : IS.iw) (p : IF.ffs * option (Z * option Z)) : IS.iw :=
  let s := IS.w_s w in let c := IS.w_c w in let r := IS.w_r w in
  let x := fx w in
  let '(f, mm) := p in
  let len := Z.shiftr (IF.f_bits f) 3 in
  let f := IF.fset_in f (IF.f_in f - len) in
  let f := IF.fset_bits f (wrap32 (IF.f_bits f - Z.shiftl len 3)) in
  let f := IF.fset_hold f (Z.land (IF.f_hold f) (IF.zmask (IF.f_bits f))) in
  let c := IS.icset_outbuf c (IF.f_ob f) in
  let c := IS.icset_next_in c (IF.f_in f) in
  let c := IS.icset_next_out c (IF.f_out f) in
  let c := IS.icset_avail_in c (wrap32 (if IF.f_in f <? IF.x_last x then 5 + (IF.x_last x - IF.f_in f)
                                        else 5 - (IF.f_in f - IF.x_last x))) in
  let c := IS.icset_avail_out c (wrap32 (if IF.f_out f <? IF.x_end x then 257 + (IF.x_end x - IF.f_out f)
                                         else 257 - (IF.f_out f - IF.x_end x))) in
  let s := IS.iset_hold s (IF.f_hold f) in
  let s := IS.iset_bits s (IF.f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (IS.iset_mode s mode, IS.icset_msg c msg)
                 | Some (mode, None) => (IS.iset_mode s mode, c)
                 | None => (s, c)
                 end in
  IS.mkW s c r.

Lemma ff_eq : forall w, IF.inflate_fast w
  = fepi w (iterZ (ffuel w) (stepS (fx w) (IS.w_s w)) (fun f => (f, None)) (ff0 w)).
Proof. intros w. unfold IF.inflate_fast, fepi, ffuel, stepS, fx, ff0. cbv beta zeta. reflexivity. Qed.

(** The epilogue's results. *)
Definition ep_bits (f : IF.ffs) : Z := wrap32 (IF.f_bits f - Z.shiftl (Z.shiftr (IF.f_bits f) 3) 3).
Definition ep_in (f : IF.ffs) : Z := IF.f_in f - Z.shiftr (IF.f_bits f) 3.
Definition ep_hold (f : IF.ffs) : Z := Z.land (IF.f_hold f) (IF.zmask (ep_bits f)).
Definition ep_ai (w : IS.iw) (f : IF.ffs) : Z :=
  wrap32 (if ep_in f <? IF.x_last (fx w) then 5 + (IF.x_last (fx w) - ep_in f)
          else 5 - (ep_in f - IF.x_last (fx w))).
Definition ep_ao (w : IS.iw) (f : IF.ffs) : Z :=
  wrap32 (if IF.f_out f <? IF.x_end (fx w) then 257 + (IF.x_end (fx w) - IF.f_out f)
          else 257 - (IF.f_out f - IF.x_end (fx w))).
Definition ep_c (w : IS.iw) (f : IF.ffs) : IS.icall :=
  IS.icset_avail_out (IS.icset_avail_in (IS.icset_next_out (IS.icset_next_in
    (IS.icset_outbuf (IS.w_c w) (IF.f_ob f)) (ep_in f)) (IF.f_out f)) (ep_ai w f)) (ep_ao w f).
Definition ep_s (w : IS.iw) (f : IF.ffs) : IS.inflate_state :=
  IS.iset_bits (IS.iset_hold (IS.w_s w) (ep_hold f)) (ep_bits f).

Lemma fepi_len : forall w f, fepi w (f, None) = IS.mkW (ep_s w f) (ep_c w f) (IS.w_r w).
Proof. reflexivity. Qed.

Lemma fepi_type : forall w f,
  fepi w (f, Some (IS.TYPE, None)) = IS.mkW (IS.iset_mode (ep_s w f) IS.TYPE) (ep_c w f) (IS.w_r w).
Proof. reflexivity. Qed.

Lemma load_mkW : forall s c r, IS.LOAD (IS.mkW s c r)
  = IS.mkW s c (IS.mkIR (IS.ic_next_in c) (IS.ic_avail_in c) (IS.ic_next_out c) (IS.ic_avail_out c)
                        (IS.is_hold s) (IS.is_bits s) (IS.ir_in r) (IS.ir_out r) (IS.ir_ret r)).
Proof. reflexivity. Qed.

Lemma restore_mkW : forall s c r, IS.RESTORE (IS.mkW s c r)
  = IS.mkW (IS.iset_bits (IS.iset_hold s (IS.ir_hold r)) (IS.ir_bits r))
           (IS.icset_avail_in (IS.icset_next_in (IS.icset_avail_out (IS.icset_next_out c (IS.ir_put r))
                                                                    (IS.ir_left r)) (IS.ir_next r))
                              (IS.ir_have r)) r.
Proof. reflexivity. Qed.

(** RT's write-back, by exit. *)
Lemma q5_len : forall st z bin bhave bnext bhold bbits obuf oput oleft qin qout qret y,
  RIF.y_exit y = RIF.ExLen ->
  fast_q5 (RI.mkInfSt st z (RB.mkBR bin bhave bnext bhold bbits) (RI.mkOB obuf oput oleft) qin qout qret) y
  = RI.mkInfSt (RI.set_bits (RI.set_hold (RI.set_bits (RI.set_hold st bhold) bbits) (RIF.y_hold y)) (RIF.y_bits y)) z
      (RB.mkBR bin (RIF.y_avail_in y) (RIF.y_in y) (RIF.y_hold y) (RIF.y_bits y))
      (RI.mkOB (RIF.y_buf y) (RIF.y_out y) (RIF.y_avail_out y)) qin qout qret.
Proof. intros. unfold fast_q5. rewrite H. reflexivity. Qed.

Lemma q5_type : forall st z bin bhave bnext bhold bbits obuf oput oleft qin qout qret y,
  RIF.y_exit y = RIF.ExType ->
  fast_q5 (RI.mkInfSt st z (RB.mkBR bin bhave bnext bhold bbits) (RI.mkOB obuf oput oleft) qin qout qret) y
  = RI.mkInfSt (RI.set_mode (RI.set_bits (RI.set_hold (RI.set_bits (RI.set_hold st bhold) bbits) (RIF.y_hold y))
                                         (RIF.y_bits y)) RI.M_TYPE) z
      (RB.mkBR bin (RIF.y_avail_in y) (RIF.y_in y) (RIF.y_hold y) (RIF.y_bits y))
      (RI.mkOB (RIF.y_buf y) (RIF.y_out y) (RIF.y_avail_out y)) qin qout qret.
Proof. intros. unfold fast_q5. rewrite H. reflexivity. Qed.

(** Hold/bits/mode writes leave the state relation's clusters, and the tables, alone. *)
Lemma icr_hb : forall s st h b h' b', ist_core_rel s st ->
  ist_core_rel (IS.iset_bits (IS.iset_hold s h) b) (RI.set_bits (RI.set_hold st h') b').
Proof.
  intros s st h b h' b' H. unfold ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  cbn [RI.set_bits RI.set_hold RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld].
  autorewrite with s5i_hold s5i_bits. exact H.
Qed.

Lemma icr_mode : forall s st m, ist_core_rel s st ->
  ist_core_rel (IS.iset_mode s (RI.m_val m)) (RI.set_mode st m).
Proof.
  intros s st m H. unfold ist_core_rel, hdr_rel, win_rel, cur_rel, tab_rel, bld_rel in *.
  cbn [RI.set_mode RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld RI.h_mode RI.h_last RI.h_wrap
       RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head].
  autorewrite with s5i_mode.
  destruct H as ((Hm & Hrest) & Hw & Hc & Ht & Hb). split; [split; [reflexivity | exact Hrest] |]. tauto.
Qed.

Lemma code_at_hold : forall s v p, IS.code_at (IS.iset_hold s v) p = IS.code_at s p.
Proof. reflexivity. Qed.
Lemma code_at_bits : forall s v p, IS.code_at (IS.iset_bits s v) p = IS.code_at s p.
Proof. reflexivity. Qed.
Lemma code_at_mode : forall s v p, IS.code_at (IS.iset_mode s v) p = IS.code_at s p.
Proof. reflexivity. Qed.
Lemma tbl_of_hold : forall st v r, RI.tbl_of (RI.set_hold st v) r = RI.tbl_of st r.
Proof. reflexivity. Qed.
Lemma tbl_of_bits : forall st v r, RI.tbl_of (RI.set_bits st v) r = RI.tbl_of st r.
Proof. reflexivity. Qed.
Lemma tbl_of_mode : forall st v r, RI.tbl_of (RI.set_mode st v) r = RI.tbl_of st r.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* Entry: the two loops start related                                        *)
(* ------------------------------------------------------------------------- *)

Lemma fast_entry : forall w q,
  icore w q -> tviews_blk w q -> xviews_blk w -> IS.ir_bits (IS.w_r w) <= 8 * IS.ir_next (IS.w_r w) ->
  RI.q_mode q = RI.M_LEN -> 6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) ->
  xrel (fx (IS.RESTORE w)) (RIF.if_ctx (fast_args q)) (IS.w_s (IS.RESTORE w))
       (IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w))
  /\ frel (IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w)) (ff0 (IS.RESTORE w)) (RIF.if_st0 (fast_args q))
  /\ rng (RIF.if_st0 (fast_args q))
  /\ RIF.f_in (RIF.if_st0 (fast_args q)) < RIF.f_last (RIF.if_ctx (fast_args q))
  /\ RIF.f_out (RIF.if_st0 (fast_args q)) < RIF.f_end (RIF.if_ctx (fast_args q))
  /\ Z.of_nat (S (Z.to_nat (RIF.f_end (RIF.if_ctx (fast_args q)) - RIF.f_out (RIF.if_st0 (fast_args q)))))
     <= ffuel (IS.RESTORE w)
  /\ 0 <= Q (RIF.if_st0 (fast_args q)).
Proof.
  intros w q Hc Ht Hx Hbn Hm H6 H258.
  destruct w as [s cw r]. destruct q as [st z [bin bhave bnext bhold bbits] [obuf oput oleft] qin qout qret].
  unfold icore, iw_rel in Hc. cbv zeta in Hc.
  cbn [IS.w_s IS.w_c IS.w_r RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret RB.br_in RB.br_have
       RB.br_next RB.br_hold RB.br_bits RI.o_buf RI.o_put RI.o_left] in Hc, Hbn, H6, H258.
  destruct Hc as ((Hcore & Hh & Hb & Hn & Hhv & Hn0 & Hhv0 & Hil & Hir & Hp & Hl & Hp0 & Hl0 & Hol & Hor
                   & Hz & Hqi & Hqo & Hqr)
                  & Hret & Hb39 & Hhold & Hbn2 & Hin & Htail & HN31 & Hnh32 & Hout & Htot & Hstot & Hwrap & Hwbits & Hhd
                  & Hsane & Hws & Hwh & Hwn & Hwb & Hflags & Hcodes & Hwbyte & Hobyte).
  pose proof Hcore as (Hhdr & Hwin & Hcur & Htab & Hbld).
  destruct Htab as (Hlc & Hdc & Hlb & Hdb & Hnx & Hcl & Hctr & Hsn).
  destruct Hwin as (Hwbt & Hwsz & Hwhv & Hwnx & Hal & Hwin2).
  unfold tviews_blk in Ht. cbv zeta in Ht. cbn [IS.w_s RI.q_st] in Ht. destruct Ht as [Hlv Hdv].
  unfold xviews_blk in Hx. cbv zeta in Hx. cbn [IS.w_s] in Hx. destruct Hx as [Hlx Hdx].
  pose proof (proj1 Hlv) as Hlr. pose proof (proj1 Hdv) as Hdr.
  rewrite restore_mkW.
  set (sR := IS.iset_bits (IS.iset_hold s (IS.ir_hold r)) (IS.ir_bits r)).
  set (cR := IS.icset_avail_in (IS.icset_next_in (IS.icset_avail_out (IS.icset_next_out cw (IS.ir_put r))
                (IS.ir_left r)) (IS.ir_next r)) (IS.ir_have r)).
  cbn [IS.w_s IS.w_r].
  assert (HQ : forall i, 0 <= i -> arr_get (IS.ic_input cw) i = bin i /\ 0 <= bin i < 256) by exact Hin.
  assert (Hw1 : wrap32 (IS.ir_have r - 5) = IS.ir_have r - 5) by (apply wrap32_id; lia).
  assert (Hw2 : wrap32 (IS.ir_out r - IS.ir_left r) = IS.ir_put r) by (rewrite Hout, wrap32_id; lia).
  assert (Hw3 : wrap32 (IS.ir_left r - 257) = IS.ir_left r - 257) by (apply wrap32_id; lia).
  conjs.
  - constructor.
    + exact HQ.
    + change (IS.ir_next r + wrap32 (IS.ir_have r - 5) = bnext + (bhave - 5)). lia.
    + change (IS.ir_put r + wrap32 (IS.ir_left r - 257) = oput + (oleft - 257)). lia.
    + change (oput + (oleft - 257) + 257 = IS.ir_put r + IS.ir_left r). lia.
    + exact HN31.
    + change (IS.ir_put r - wrap32 (IS.ir_out r - IS.ir_left r) = 0). lia.
    + change (oput - (qout - oleft) = 0). lia.
    + change (RI.w_whave (RI.s_win st) = 0). congruence.
    + change (RI.t_sane (RI.s_tab st) = 1). congruence.
    + change (IF.zmask (IS.is_lenbits s) = Z.shiftl 1 (RI.t_lenbits (RI.s_tab st)) - 1).
      rewrite fk_zmask by lia. congruence.
    + change (Z.shiftl 1 (RI.t_lenbits (RI.s_tab st)) - 1 = Z.shiftl 1 (IS.is_lenbits s) - 1). congruence.
    + change (IF.zmask (IS.is_distbits s) = Z.shiftl 1 (RI.t_distbits (RI.s_tab st)) - 1).
      rewrite fk_zmask by lia. congruence.
    + change (Z.shiftl 1 (RI.t_distbits (RI.s_tab st)) - 1 = Z.shiftl 1 (IS.is_distbits s) - 1). congruence.
    + unfold sR. rewrite code_at_bits, code_at_hold. autorewrite with s5i_hold s5i_bits. exact Hlv.
    + unfold sR. rewrite code_at_bits, code_at_hold. autorewrite with s5i_hold s5i_bits. exact Hdv.
    + unfold sR. rewrite code_at_bits, code_at_hold. autorewrite with s5i_hold s5i_bits. exact Hlx.
    + unfold sR. rewrite code_at_bits, code_at_hold. autorewrite with s5i_hold s5i_bits. exact Hdx.
  - constructor.
    + change (IS.ir_next r = bnext). exact Hn.
    + change (IS.ir_put r = oput). exact Hp.
    + change (IS.ir_hold r = bhold). exact Hh.
    + change (IS.ir_bits r = bbits). exact Hb.
    + change (arr_len (IS.ic_outbuf cw) = IS.ir_put r + IS.ir_left r). exact Hol.
    + change (arr_rel (IS.ic_outbuf cw) obuf 0 (IS.ir_put r + IS.ir_left r)).
      intros i Hi. destruct (Z_lt_le_dec i (IS.ir_put r)); [apply Hor | apply Htail]; lia.
  - constructor; cbn [RIF.if_st0 RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits fast_args RIF.a_next_in
                      RIF.a_next_out RIF.a_hold RIF.a_bits RI.q_restore RI.qset_st RI.q_st RI.q_br RI.q_ob
                      RI.set_bits RI.set_hold RI.s_hold RI.s_bits RB.br_next RB.br_hold RB.br_bits RI.o_put];
      subst; lia.
  - change (bnext < bnext + (bhave - 5)). lia.
  - change (oput < oput + (oleft - 257)). lia.
  - change (Z.of_nat (S (Z.to_nat (oput + (oleft - 257) - oput))) <= 8 * IS.ir_have r + IS.ir_left r + 80).
    lia.
  - unfold Q. change (0 <= 8 * bnext - bbits). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Exit: the post-state                                                      *)
(* ------------------------------------------------------------------------- *)

Lemma fast_post : forall w q fE s' e mm,
  icore w q -> tviews_blk w q -> xviews_blk w -> IS.ir_bits (IS.w_r w) <= 8 * IS.ir_next (IS.w_r w) ->
  RI.q_mode q = RI.M_LEN -> 6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) ->
  (e = RIF.ExLen /\ mm = None \/ e = RIF.ExType /\ mm = Some (IS.TYPE, None)) ->
  iterZ (ffuel (IS.RESTORE w)) (stepS (fx (IS.RESTORE w)) (IS.w_s (IS.RESTORE w))) (fun f => (f, None))
        (ff0 (IS.RESTORE w)) = (fE, mm) ->
  frel (IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w)) fE s' -> rng s' ->
  Q (RIF.if_st0 (fast_args q)) <= Q s' <= 8 * (RIF.f_last (RIF.if_ctx (fast_args q)) + 5) ->
  RIF.f_out (RIF.if_st0 (fast_args q)) <= RIF.f_out s' <= IS.ir_put (IS.w_r w) + IS.ir_left (IS.w_r w) ->
  zbytes (RIF.f_buf s') ->
  icore (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q (RIF.if_finish (RIF.if_ctx (fast_args q)) s' e))
  /\ tviews_blk (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q (RIF.if_finish (RIF.if_ctx (fast_args q)) s' e))
  /\ xviews_blk (IS.LOAD (IF.inflate_fast (IS.RESTORE w)))
  /\ IS.ir_bits (IS.w_r (IS.LOAD (IF.inflate_fast (IS.RESTORE w))))
     <= 8 * IS.ir_next (IS.w_r (IS.LOAD (IF.inflate_fast (IS.RESTORE w)))).
Proof.
  intros w q fE s' e mm Hc Ht Hx Hbn Hm H6 H258 Hem Hit F' R' HQ HO Hbs. unfold zbytes in Hbs.
  destruct w as [s cw r]. destruct q as [st z [bin bhave bnext bhold bbits] [obuf oput oleft] qin qout qret].
  unfold icore, iw_rel in Hc. cbv zeta in Hc.
  cbn [IS.w_s IS.w_c IS.w_r RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret RB.br_in RB.br_have
       RB.br_next RB.br_hold RB.br_bits RI.o_buf RI.o_put RI.o_left RI.q_mode] in Hc, Hbn, H6, H258, F', HO, Hm.
  destruct Hc as ((Hcore & Hh & Hb & Hn & Hhv & Hn0 & Hhv0 & Hil & Hir & Hp & Hl & Hp0 & Hl0 & Hol & Hor
                   & Hz & Hqi & Hqo & Hqr)
                  & Hret & Hb39 & Hhold & Hbn2 & Hin & Htail & HN31 & Hnh32 & Hout & Htot & Hstot & Hwrap & Hwbits & Hhd
                  & Hsane & Hws & Hwh & Hwn & Hwb & Hflags & Hcodes & Hwbyte & Hobyte).
  unfold tviews_blk in Ht. cbv zeta in Ht. cbn [IS.w_s RI.q_st] in Ht. destruct Ht as [Hlv Hdv].
  unfold xviews_blk in Hx. cbv zeta in Hx. cbn [IS.w_s] in Hx. destruct Hx as [Hlx Hdx].
  pose proof Hcore as (Hhdr & _).
  assert (Hmode : IS.is_mode s = RI.m_val RI.M_LEN) by (rewrite <- Hm; exact (proj1 Hhdr)).
  destruct (Hflags ltac:(rewrite Hmode; discriminate)) as [Hfl Hck].
  (* the loop's exit values *)
  destruct R' as [RbE RhE RiE RoE].
  pose proof (fr_in _ _ _ F') as FiE. pose proof (fr_out _ _ _ F') as FoE.
  pose proof (fr_hold _ _ _ F') as FhE. pose proof (fr_bits _ _ _ F') as FbE.
  pose proof (fr_len _ _ _ F') as FlE. pose proof (fr_buf _ _ _ F') as FrE.
  unfold Q in HQ. cbn [RIF.if_st0 RIF.f_in RIF.f_out RIF.f_bits RIF.f_last RIF.if_ctx fast_args RIF.a_next_in
                       RIF.a_avail_in RIF.a_next_out RIF.a_bits RI.q_restore RI.qset_st RI.q_st RI.q_br RI.q_ob
                       RI.set_bits RI.set_hold RI.s_bits RB.br_next RB.br_have RB.br_bits RI.o_put] in HQ, HO.
  set (N := IS.ir_put r + IS.ir_left r) in *.
  set (BE := RIF.f_bits s') in *. set (IE := RIF.f_in s') in *.
  set (HE := RIF.f_hold s') in *. set (OE := RIF.f_out s') in *.
  assert (Hsh : Z.shiftr BE 3 = BE / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Hsl : Z.shiftl (BE / 8) 3 = BE / 8 * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  pose proof (Z.div_mod BE 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound BE 8 ltac:(lia)) as Hmb.
  assert (Hbits : ep_bits fE = BE mod 8).
  { unfold ep_bits. rewrite FbE, Hsh, Hsl. rewrite wrap32_id; lia. }
  assert (Hepin : ep_in fE = IE - BE / 8) by (unfold ep_in; rewrite FiE, FbE, Hsh; reflexivity).
  assert (Hhold' : ep_hold fE = Z.land HE (Z.shiftl 1 (BE mod 8) - 1)).
  { unfold ep_hold. rewrite Hbits, FhE, fk_zmask by lia. reflexivity. }
  rewrite restore_mkW in Hit |- *.
  set (sR := IS.iset_bits (IS.iset_hold s (IS.ir_hold r)) (IS.ir_bits r)) in *.
  set (cR := IS.icset_avail_in (IS.icset_next_in (IS.icset_avail_out (IS.icset_next_out cw (IS.ir_put r))
                (IS.ir_left r)) (IS.ir_next r)) (IS.ir_have r)) in *.
  assert (Hlast : IF.x_last (fx (IS.mkW sR cR r)) = bnext + (bhave - 5)).
  { change (IS.ir_next r + wrap32 (IS.ir_have r - 5) = bnext + (bhave - 5)). rewrite wrap32_id; lia. }
  assert (Hend : IF.x_end (fx (IS.mkW sR cR r)) = N - 257).
  { change (IS.ir_put r + wrap32 (IS.ir_left r - 257) = N - 257). rewrite wrap32_id; unfold N; lia. }
  assert (Hai : ep_ai (IS.mkW sR cR r) fE = bnext + bhave - (IE - BE / 8)).
  { unfold ep_ai. rewrite Hlast, Hepin. destruct (_ <? _); rewrite wrap32_id; lia. }
  assert (Hao : ep_ao (IS.mkW sR cR r) fE = N - OE).
  { unfold ep_ao. rewrite Hend, FoE. destruct (_ <? _); rewrite wrap32_id; unfold N in *; lia. }
  rewrite ff_eq, Hit.
  (* RT's epilogue values *)
  set (Q0 := RI.mkInfSt st z (RB.mkBR bin bhave bnext bhold bbits) (RI.mkOB obuf oput oleft) qin qout qret) in *.
  set (c0 := RIF.if_ctx (fast_args Q0)) in *.
  assert (Ey_bits : RIF.y_bits (RIF.if_finish c0 s' e) = BE mod 8).
  { change (RBa.u32 (BE - Z.shiftl (Z.shiftr BE 3) 3) = BE mod 8).
    rewrite <- fk_wrap32_u32, Hsh, Hsl, wrap32_id; lia. }
  assert (Ey_in : RIF.y_in (RIF.if_finish c0 s' e) = IE - BE / 8).
  { change (IE - Z.shiftr BE 3 = IE - BE / 8). now rewrite Hsh. }
  assert (Ey_hold : RIF.y_hold (RIF.if_finish c0 s' e) = Z.land HE (Z.shiftl 1 (BE mod 8) - 1)).
  { change (Z.land HE (Z.shiftl 1 (RBa.u32 (BE - Z.shiftl (Z.shiftr BE 3) 3)) - 1)
            = Z.land HE (Z.shiftl 1 (BE mod 8) - 1)).
    rewrite <- fk_wrap32_u32, Hsh, Hsl, wrap32_id by lia. do 3 f_equal. lia. }
  assert (Ey_ai : RIF.y_avail_in (RIF.if_finish c0 s' e) = bnext + bhave - (IE - BE / 8)).
  { change (RBa.u32 (if IE - Z.shiftr BE 3 <? bnext + (bhave - 5)
                     then 5 + (bnext + (bhave - 5) - (IE - Z.shiftr BE 3))
                     else 5 - (IE - Z.shiftr BE 3 - (bnext + (bhave - 5))))
            = bnext + bhave - (IE - BE / 8)).
    rewrite Hsh. destruct (_ <? _); rewrite RBa.u32_id; lia. }
  assert (Ey_ao : RIF.y_avail_out (RIF.if_finish c0 s' e) = N - OE).
  { change (RBa.u32 (if OE <? oput + (oleft - 257) then 257 + (oput + (oleft - 257) - OE)
                     else 257 - (OE - (oput + (oleft - 257)))) = N - OE).
    destruct (_ <? _); rewrite RBa.u32_id; unfold N in *; lia. }
  assert (Ey_out : RIF.y_out (RIF.if_finish c0 s' e) = OE) by reflexivity.
  assert (Ey_buf : RIF.y_buf (RIF.if_finish c0 s' e) = RIF.f_buf s') by reflexivity.
  assert (Ey_exit : RIF.y_exit (RIF.if_finish c0 s' e) = e) by reflexivity.
  destruct Hem as [[-> ->]|[-> ->]].
  - rewrite fepi_len, load_mkW. unfold Q0. rewrite q5_len by exact Ey_exit. fold Q0.
    rewrite Ey_bits, Ey_in, Ey_hold, Ey_ai, Ey_ao, Ey_out, Ey_buf.
    unfold icore, iw_rel, zstrm_rel, tviews_blk, xviews_blk. cbv zeta.
    cbn [IS.w_s IS.w_c IS.w_r RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret RB.br_in RB.br_have
         RB.br_next RB.br_hold RB.br_bits RI.o_buf RI.o_put RI.o_left IS.ir_next IS.ir_have IS.ir_put
         IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret].
    unfold ep_s, ep_c. rewrite Hai, Hao, Hepin, Hhold', Hbits.
    unfold sR, cR. cbn [IS.w_s IS.w_c].
    autorewrite with s5i_hold s5i_bits s5ic_avail_out s5ic_avail_in s5ic_next_out s5ic_next_in s5ic_outbuf.
    unfold zstrm_rel in Hz.
    conjs.
    all: try solve [ reflexivity | assumption | lia | (apply icr_hb; apply icr_hb; exact Hcore)
                   | (cbn [RI.s_tab RI.set_bits RI.set_hold]; assumption)
                   | (intros; split; assumption)
                   | (rewrite ?code_at_bits, ?code_at_hold, ?tbl_of_bits, ?tbl_of_hold;
                      cbn [RI.s_tab RI.set_bits RI.set_hold]; assumption)
                   | (rewrite FoE; apply (arr_rel_narrow _ _ 0 N); [lia | lia | exact FrE])
                   | (apply fk_low_range; lia)
                   | exact Hbs
                   | (cbn [RI.s_win RI.set_bits RI.set_hold]; exact Hwbyte) ].
  - rewrite fepi_type, load_mkW. unfold Q0. rewrite q5_type by exact Ey_exit. fold Q0.
    rewrite Ey_bits, Ey_in, Ey_hold, Ey_ai, Ey_ao, Ey_out, Ey_buf.
    unfold icore, iw_rel, zstrm_rel, tviews_blk, xviews_blk. cbv zeta.
    cbn [IS.w_s IS.w_c IS.w_r RI.q_st RI.q_br RI.q_ob RI.q_z RI.q_in RI.q_out RI.q_ret RB.br_in RB.br_have
         RB.br_next RB.br_hold RB.br_bits RI.o_buf RI.o_put RI.o_left IS.ir_next IS.ir_have IS.ir_put
         IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out IS.ir_ret].
    unfold ep_s, ep_c. rewrite Hai, Hao, Hepin, Hhold', Hbits.
    unfold sR, cR. cbn [IS.w_s IS.w_c].
    autorewrite with s5i_mode s5i_hold s5i_bits s5ic_avail_out s5ic_avail_in s5ic_next_out s5ic_next_in
                     s5ic_outbuf.
    unfold zstrm_rel in Hz.
    conjs.
    all: try solve [ reflexivity | assumption | lia
                   | (apply (icr_mode _ _ RI.M_TYPE); apply icr_hb; apply icr_hb; exact Hcore)
                   | (cbn [RI.s_tab RI.set_mode RI.set_bits RI.set_hold]; assumption)
                   | (intros; split; assumption)
                   | (rewrite ?code_at_mode, ?code_at_bits, ?code_at_hold, ?tbl_of_mode, ?tbl_of_bits,
                        ?tbl_of_hold; cbn [RI.s_tab RI.set_mode RI.set_bits RI.set_hold]; assumption)
                   | (rewrite FoE; apply (arr_rel_narrow _ _ 0 N); [lia | lia | exact FrE])
                   | (apply fk_low_range; lia)
                   | exact Hbs
                   | (cbn [RI.s_win RI.set_mode RI.set_bits RI.set_hold]; exact Hwbyte) ].
Qed.

(* ------------------------------------------------------------------------- *)
(* The fast path                                                             *)
(* ------------------------------------------------------------------------- *)

(** RT's [if_model] by exit.  The [Qed] hazard of [RIF.if_step_unfold]'s note applies to
    [if_model] too: [unfold]ing it on the concrete [fast_args q] made the kernel hang at
    [Qed] (> 280 s).  Stated over an abstract [a] and rewritten with a [reflexivity]
    lemma, it checks at once. *)
Lemma if_model_eq : forall a, RIF.if_model a =
  match RIF.if_loop (S (Z.to_nat (RIF.f_end (RIF.if_ctx a) - RIF.f_out (RIF.if_st0 a)))) (RIF.if_ctx a)
          (RIF.if_st0 a) with
  | Some (RIF.IfStop s')  => Some (RIF.if_finish (RIF.if_ctx a) s' RIF.ExLen)
  | Some (RIF.IfEob s')   => Some (RIF.if_finish (RIF.if_ctx a) s' RIF.ExType)
  | Some (RIF.IfBad s' m) => Some (RIF.if_finish (RIF.if_ctx a) s' (RIF.ExBad m))
  | Some (RIF.IfCont _)   => None
  | Some RIF.IfFuel       => None
  | None                  => None
  end.
Proof. intros a. reflexivity. Qed.

Lemma if_model_cases : forall a y, RIF.if_model a = Some y -> (forall m, RIF.y_exit y <> RIF.ExBad m) ->
  exists s', (RIF.if_loop (S (Z.to_nat (RIF.f_end (RIF.if_ctx a) - RIF.f_out (RIF.if_st0 a)))) (RIF.if_ctx a)
                (RIF.if_st0 a) = Some (RIF.IfStop s') /\ y = RIF.if_finish (RIF.if_ctx a) s' RIF.ExLen)
          \/ (RIF.if_loop (S (Z.to_nat (RIF.f_end (RIF.if_ctx a) - RIF.f_out (RIF.if_st0 a)))) (RIF.if_ctx a)
                (RIF.if_st0 a) = Some (RIF.IfEob s') /\ y = RIF.if_finish (RIF.if_ctx a) s' RIF.ExType).
Proof.
  intros a y Hy Hnb. rewrite if_model_eq in Hy.
  destruct (RIF.if_loop (S (Z.to_nat (RIF.f_end (RIF.if_ctx a) - RIF.f_out (RIF.if_st0 a)))) (RIF.if_ctx a)
              (RIF.if_st0 a)) as [[s'|s'|s'|s' m|]|]; try discriminate Hy.
  - injection Hy as <-. exists s'. left. split; reflexivity.
  - injection Hy as <-. exists s'. right. split; reflexivity.
  - injection Hy as <-. exfalso. exact (Hnb m eq_refl).
Qed.

(** [inflate_fast_sim] with the two facts it lacks (NEEDS.md N1-N3), both carried to the
    post-state. *)
Lemma inflate_fast_sim_x : forall w q y,
  icore w q -> tviews_blk w q -> xviews_blk w -> IS.ir_bits (IS.w_r w) <= 8 * IS.ir_next (IS.w_r w) ->
  RI.q_mode q = RI.M_LEN ->
  6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) ->
  RIF.if_model (fast_args q) = Some y -> (forall m, RIF.y_exit y <> RIF.ExBad m) ->
  icore (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q y)
  /\ tviews_blk (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q y)
  /\ xviews_blk (IS.LOAD (IF.inflate_fast (IS.RESTORE w)))
  /\ IS.ir_bits (IS.w_r (IS.LOAD (IF.inflate_fast (IS.RESTORE w))))
     <= 8 * IS.ir_next (IS.w_r (IS.LOAD (IF.inflate_fast (IS.RESTORE w)))).
Proof.
  intros w q y Hc Ht Hx Hbn Hm H6 H258 Hy Hnb.
  destruct (fast_entry w q Hc Ht Hx Hbn Hm H6 H258) as (HX & HF0 & HR0 & Hg1 & Hg2 & Hfuel & HQ0).
  assert (Hwb : zbytes (RIF.f_window (RIF.if_ctx (fast_args q)))).
  { pose proof Hc as Hc'. unfold icore in Hc'. cbv zeta in Hc'.
    repeat match type of Hc' with _ /\ (_ /\ _) => apply proj2 in Hc' end. exact (proj1 Hc'). }
  assert (Hob : zbytes (RIF.f_buf (RIF.if_st0 (fast_args q)))).
  { pose proof Hc as Hc'. unfold icore in Hc'. cbv zeta in Hc'.
    repeat match type of Hc' with _ /\ (_ /\ _) => apply proj2 in Hc' end. exact (proj2 Hc'). }
  destruct (if_model_cases _ _ Hy Hnb) as (s' & [[Hl ->]|[Hl ->]]).
  - pose proof (fast_loop_bytes _ _ _ _ Hwb Hob Hl) as Hbs. cbn [bstep] in Hbs.
    pose proof (fl_loop _ _ _ _ HX _ _ _ _ _ HF0 HR0 Hg1 Hg2 Hfuel Hl) as HL.
    destruct HL as (fE & Hit & F' & R' & HQ & HO).
    exact (fast_post w q fE s' RIF.ExLen None Hc Ht Hx Hbn Hm H6 H258
             (or_introl (conj eq_refl eq_refl)) Hit F' R' HQ HO Hbs).
  - pose proof (fast_loop_bytes _ _ _ _ Hwb Hob Hl) as Hbs. cbn [bstep] in Hbs.
    pose proof (fl_loop _ _ _ _ HX _ _ _ _ _ HF0 HR0 Hg1 Hg2 Hfuel Hl) as HL.
    destruct HL as (fE & Hit & F' & R' & HQ & HO).
    exact (fast_post w q fE s' RIF.ExType (Some (IS.TYPE, None)) Hc Ht Hx Hbn Hm H6 H258
             (or_intror (conj eq_refl eq_refl)) Hit F' R' HQ HO Hbs).
Qed.

(** [IInv.tent] carries [xent], so [tviews_blk] gives [xviews_blk]. *)
Lemma xviews_of_tviews : forall w q, tviews_blk w q -> xviews_blk w.
Proof.
  intros w q [Hl Hd]. split.
  - exact (xview_of_tview _ _ _ _ (tent_xent KLens) Hl).
  - exact (xview_of_tview _ _ _ _ (tent_xent KDists) Hd).
Qed.

(** The fast path, up to the [set_back] that LEN does after it on an end of block.  A
    corollary of [inflate_fast_sim_x]: [icore] gives [ir_bits <= 8 * ir_next] and [tent]
    gives [xviews_blk] (NEEDS.md N1-N3, adopted in IInv). *)
Lemma inflate_fast_sim : forall w q y,
  icore w q -> tviews_blk w q -> RI.q_mode q = RI.M_LEN ->
  6 <= RB.br_have (RI.q_br q) -> 258 <= RI.o_left (RI.q_ob q) ->
  RIF.if_model (fast_args q) = Some y -> (forall m, RIF.y_exit y <> RIF.ExBad m) ->
  icore (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q y)
  /\ tviews_blk (IS.LOAD (IF.inflate_fast (IS.RESTORE w))) (fast_q5 q y).
Proof.
  intros w q y Hc Ht Hm H6 H258 Hy Hnb.
  assert (Hbn : IS.ir_bits (IS.w_r w) <= 8 * IS.ir_next (IS.w_r w)).
  { pose proof Hc as Hc'. unfold icore in Hc'. cbv zeta in Hc'.
    destruct Hc' as (_ & _ & _ & _ & Hbn & _). exact Hbn. }
  destruct (inflate_fast_sim_x w q y Hc Ht (xviews_of_tviews w q Ht) Hbn Hm H6 H258 Hy Hnb)
    as (Hc' & Ht' & _ & _).
  split; [exact Hc' | exact Ht'].
Qed.
