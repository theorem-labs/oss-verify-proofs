(** * Bridge.Infl.ITop — group I's deliverable: [IBoundary.BrUncompressCall].

    zlib 1.4: S5's inflate is now 1.4's and is related to
    RT's 1.4 flavour, so the deliverable is [IBoundary14.BrUncompressCall14], stated with
    [ZRepro14.zr_inflate14]; the text below is the 1.3.1 one with the RT call at 1.4.

    Owner: the part C lead, by the TL's split of group I.  The harness's
    first uncompress call is one [inflate] on S5's fresh state with the whole input and
    [avail_out = n]; RT's [zr_inflate] is one [inflate_model] call.  When RT's call returns
    [Z_STREAM_END] with bytes [x], S5's returns [Z_STREAM_END], the same bytes and
    [total_out = |x|]:

    - entry ([ITopEntry]): the two loop-entry states satisfy [IInv.inv], RT's context is
      [ctx_rel FL];
    - RT's loop ends in [InfLeave qf] with [q_ret qf = Z_STREAM_END] ([ITopExit.rt_leave_ret]; an
      [InfRet] code is never [Z_STREAM_END]: [ILoop.loop_ret]);
    - the loops ([ILoop.loop_ok], any S5 fuel at least RT's trip count; S5's own fuel is
      reconciled by [IFuelInfl.fuel_inf_loop], whose precondition is S5's
      [RefInflateEqS.WINV_entry'] at the entry);
    - the exits ([ITopExit.s5_leave], [ITopExit.rt_leave]): both return [[0, put)] of their
      output buffers, related by [iw_rel].

    Kernel cost: every unfolding of a harness-level call is stated once, over ABSTRACT states
    ([zr_inflate_init], [rt_call_eq], [zic_inflate_eq], [inflate_p_eq], [s5_call_gen]) and used
    by [rewrite]; a conversion whose scrutinee is the call on the CONCRETE fresh state makes the
    kernel evaluate inflate symbolically (it did not finish in 10 minutes). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState Inflate ZApiInst ZApiInstC HarnessSmall
  RefInflate_runA RefInflateSafeD RefInflateEqS RefZApi ZApiOk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsIn Inflate Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZRepro ZRepro14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl IFuelInfl IRelInfl14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require IBoundary IBoundary14.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv ILoop ITopEntry ITopExit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module HS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.HarnessSmall.
Module ZAC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ZApiInstC.
Module EqS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefInflateEqS.

(* The fresh states are computed constants; facts about them are [ITopEntry]'s lemmas. *)
Local Strategy opaque [ZApiInst.is0 ZApiInst.iz0 rt_st0 rt_z0].

(* ------------------------------------------------------------------------- *)
(* RT                                                                        *)
(* ------------------------------------------------------------------------- *)

Lemma zr_inflate_init : forall flush wb cap enc z s,
  RI.inflateInit2 RCo.z_fresh RCo.state_fresh wb = Some (z, s) ->
  ZRepro14.zr_inflate14 flush wb cap enc
  = match ZRepro14.zr_inf_call14 flush s z enc cap with
    | None => None
    | Some (ret, _, _, _, out) => if Z.eqb ret RBa.Z_STREAM_END then Some out else None
    end.
Proof. intros flush wb cap enc z s H. unfold ZRepro14.zr_inflate14. rewrite H. reflexivity. Qed.

(** RT's call, unfolded once ([ZRepro14.zr_inf_call14] and [Inflate14.inflate_model14]). *)
Lemma rt_call_eq : forall z s enc n,
  ZRepro14.zr_inf_call14 0 s z enc n
  = match RI14.inf_loop14 (RI.inf_fuel (RI.inf_st0 (rt_args' z s enc n))) (RI.inf_ctx (rt_args' z s enc n))
                      (RI.inf_st0 (rt_args' z s enc n)) with
    | Some (RI.InfRet q r) =>
        Some (r, CH.zlen enc - RB.br_have (RI.q_br q), RI.q_st q, RI.q_z q,
              RI.ob_slice (RI.q_ob q) 0 (RI.o_put (RI.q_ob q)))
    | Some (RI.InfLeave q) =>
        let '(q', r) := RI.inf_leave (RI.inf_ctx (rt_args' z s enc n)) q in
        Some (r, CH.zlen enc - RB.br_have (RI.q_br q'), RI.q_st q', RI.q_z q',
              RI.ob_slice (RI.q_ob q') 0 (RI.o_put (RI.q_ob q')))
    | _ => None
    end.
Proof.
  intros z s enc n. unfold ZRepro14.zr_inf_call14. fold (rt_args' z s enc n).
  unfold RI14.inflate_model14. cbv zeta.
  change (RI.g_state_null (rt_args' z s enc n) || RI.g_out_null (rt_args' z s enc n)
          || (RI.g_in_null (rt_args' z s enc n) && negb (RI.g_avail_in (rt_args' z s enc n) =? 0)))
    with false.
  cbv beta iota.
  destruct (RI14.inf_loop14 _ _ _) as [[q|q|q r|m|]|]; cbv beta iota; try reflexivity.
  destruct (RI.inf_leave _ q) as [q' r]. reflexivity.
Qed.

(** RT's side: [zr_inflate] succeeds only through a loop exit with [Z_STREAM_END] (an [InfRet]
    code never is: [ILoop.loop_ret]), and its bytes are the exit state's [[0, put)]. *)
Lemma rt_side : forall n enc x,
  Forall (fun b => 0 <= b < 256) enc -> zlength enc < 2 ^ 32 -> 0 <= n < 2 ^ 31 ->
  ZRepro14.zr_inflate14 0 15 n enc = Some x ->
  exists qf q',
    RI14.inf_loop14 (RI.inf_fuel (RI.inf_st0 (rt_args enc n))) (RI.inf_ctx (rt_args enc n))
                (RI.inf_st0 (rt_args enc n)) = Some (RI.InfLeave qf)
    /\ RI.q_ret qf = RBa.Z_STREAM_END
    /\ RI.inf_leave (RI.inf_ctx (rt_args enc n)) qf = (q', RBa.Z_STREAM_END)
    /\ x = RI.ob_slice (RI.q_ob q') 0 (RI.o_put (RI.q_ob q')).
Proof.
  intros n enc x Hb Hlen Hn Hx.
  pose proof (entry_inv enc n Hb Hlen Hn) as Hinv. pose proof (entry_ctx enc n) as Hc.
  rewrite (zr_inflate_init 0 15 n enc rt_z0 rt_st0 rt_init_eq), (rt_call_eq rt_z0 rt_st0 enc n) in Hx.
  change (rt_args' rt_z0 rt_st0 enc n) with (rt_args enc n) in Hx.
  destruct (RI14.inf_loop14 _ _ _) as [[qf|qf|qf rc|m|]|] eqn:EL; cbv beta iota in Hx; try discriminate Hx.
  2:{ destruct (rc =? _) eqn:Erc; [|discriminate Hx].
      apply Z.eqb_eq in Erc. exfalso. exact (loop_ret _ _ _ _ qf rc Hc Hinv EL Erc). }
  destruct (RI.inf_leave _ qf) as [q' r] eqn:EV. cbv beta iota in Hx.
  destruct (r =? _) eqn:Er; [|discriminate Hx]. apply Z.eqb_eq in Er.
  injection Hx as <-.
  exists qf, q'. split; [reflexivity|]. split.
  - apply (rt_leave_ret (RI.inf_ctx (rt_args enc n))). rewrite EV. exact Er.
  - split; [|reflexivity]. rewrite EV. f_equal. exact Er.
Qed.

(* ------------------------------------------------------------------------- *)
(* S5                                                                        *)
(* ------------------------------------------------------------------------- *)

(** S5's loop from the call's entry state leaves in a state [ifin]-related to RT's exit:
    [ILoop.loop_ok] at fuel [F + k] (RT's trip count [k]), and [IFuelInfl.fuel_inf_loop] for
    S5's own fuel [F], under S5's loop invariant at the entry ([RefInflateEqS.WINV_entry']). *)
Lemma s5_loop : forall n enc k qf,
  Forall (fun b => 0 <= b < 256) enc -> zlength enc < 2 ^ 32 -> 0 <= n < 2 ^ 31 ->
  RI14.inf_loop14 k (RI.inf_ctx (rt_args enc n)) (RI.inf_st0 (rt_args enc n)) = Some (RI.InfLeave qf) ->
  RI.q_ret qf = RBa.Z_STREAM_END ->
  exists wf, IA.inf_loop IS.ivar_ref Z_NO_FLUSH (RefInflate_runA.W0 ZApiInst.is0 (hc_call enc n))
             = (IA.SLeave, wf) /\ ifin wf qf.
Proof.
  intros n enc k qf Hb Hlen Hn EL Hret.
  pose proof (entry_inv enc n Hb Hlen Hn) as Hinv. pose proof (entry_ctx enc n) as Hc.
  assert (HZC : EqS.ZC (hc_call enc n))
    by (unfold EqS.ZC, hc_call; cbn [zc_avail_out zc_input]; split; [lia | split; [lia | exact Hb]]).
  destruct (EqS.WINV_entry' ZApiInst.is0 (hc_call enc n) ZApiOk.INV_is0 HZC) as [HW HP].
  set (w0 := RefInflate_runA.W0 ZApiInst.is0 (hc_call enc n)) in *.
  assert (HF : 0 <= inf_loop_fuel w0).
  { unfold inf_loop_fuel, w0, RefInflate_runA.W0, hc_call.
    cbn [IS.w_c IS.icall_of_zcall IS.ic_avail_in IS.ic_avail_out zc_input zc_avail_out].
    pose proof (zlength_nonneg enc). lia. }
  destruct (loop_ok k _ _ w0 qf Hc Hinv EL Hret (inf_loop_fuel w0 + Z.of_nat k) ltac:(lia))
    as (wf & Ewf & Hfin).
  exists wf. split; [|exact Hfin].
  rewrite inf_loop_n_eq, <- (fuel_inf_loop Z_NO_FLUSH w0 (Z.of_nat k) HW HP ltac:(lia)). exact Ewf.
Qed.

Lemma zic_inflate_eq : forall inp x aout ok,
  ZAC.zic_inflate inp x aout ok
  = (let '(r, _) := HS.inflate_p (ZApiInst.wans ok) (ZApiInst.iz_s x)
                       (mkZCall inp aout (ZApiInst.iz_z x)) Z_NO_FLUSH in
     let '(s', zr) := r in
     (ZApiInst.mkIZ s' (zr_strm zr), zr_consumed zr, zr_output zr, zr_rc zr)).
Proof. reflexivity. Qed.

Lemma zi_init_s : ZApiInst.iz_s ZApiInst.zi_init = ZApiInst.is0.
Proof. reflexivity. Qed.
Lemma zi_init_z : ZApiInst.iz_z ZApiInst.zi_init = ZApiInst.iz0.
Proof. reflexivity. Qed.

Lemma inflate_p_eq : forall ans s zc flush,
  HS.inflate_p ans s zc flush
  = match SI.inflate_m IS.ivar_ref HS.dhooks s zc flush [ans] with
    | MRet (r, chs') => (r, match chs' with [] => true | _ => false end)
    | _ => ((s, zret0 (zc_strm zc) Z_STREAM_ERROR), false)
    end.
Proof. reflexivity. Qed.

(** S5's [inflate_m], from any state whose loop leaves in an [ifin] state. *)
Lemma s5_call_gen : forall (St : Type) (hooks : zhooks St) s0 zc wf qf (chs : St),
  SI.inflateStateCheck s0 = false ->
  IA.inf_loop IS.ivar_ref Z_NO_FLUSH (RefInflate_runA.W0 s0 zc) = (IA.SLeave, wf) ->
  ifin wf qf -> RI.q_ret qf = RBa.Z_STREAM_END ->
  exists s' zr, SI.inflate_m IS.ivar_ref hooks s0 zc Z_NO_FLUSH chs = MRet ((s', zr), chs)
    /\ zr_output zr = arr_slice (IS.ic_outbuf (IS.w_c wf)) 0 (IS.ir_put (IS.w_r wf))
    /\ zr_rc zr = Z_STREAM_END
    /\ zs_total_out (zr_strm zr) = IS.ir_put (IS.w_r wf).
Proof.
  intros St hooks s0 zc wf qf chs Hchk Ewf Hfin Hret.
  rewrite RefInflate_runA.inflate_m_W0 by exact Hchk. rewrite Ewf. cbv beta iota.
  exact (s5_leave St hooks wf qf chs Hfin Hret).
Qed.

(** S5's call: the harness's [zic_inflate] on the fresh state. *)
Lemma s5_call : forall n enc wf qf,
  IA.inf_loop IS.ivar_ref Z_NO_FLUSH (RefInflate_runA.W0 ZApiInst.is0 (hc_call enc n)) = (IA.SLeave, wf) ->
  ifin wf qf -> RI.q_ret qf = RBa.Z_STREAM_END ->
  let '(is', _, out, rc) := ZAC.zic_inflate enc ZApiInst.zi_init n true in
  out = arr_slice (IS.ic_outbuf (IS.w_c wf)) 0 (IS.ir_put (IS.w_r wf)) /\ rc = 1
  /\ zs_total_out (ZApiInst.iz_z is') = IS.ir_put (IS.w_r wf).
Proof.
  intros n enc wf qf Ewf Hfin Hret.
  pose proof is0_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hchk).
  destruct (s5_call_gen _ HS.dhooks ZApiInst.is0 (hc_call enc n) wf qf [ZApiInst.wans true]
              Hchk Ewf Hfin Hret) as (s' & zr & E & Hout & Hrc & Htot).
  rewrite zic_inflate_eq, zi_init_s, zi_init_z, inflate_p_eq.
  change (mkZCall enc n ZApiInst.iz0) with (hc_call enc n).
  rewrite E. cbv beta iota. cbn [ZApiInst.iz_z].
  split; [exact Hout|]. split; [rewrite Hrc; reflexivity|]. exact Htot.
Qed.

(* ------------------------------------------------------------------------- *)
(* The deliverable                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem br_uncompress_call : IBoundary14.BrUncompressCall14.
Proof.
  intros n enc x Hn Hb Hlen Hx.
  assert (Hlen' : zlength enc < 2 ^ 32) by (unfold ZApiC.ZC_UMAX in Hlen; lia).
  destruct (rt_side n enc x Hb Hlen' ltac:(lia) Hx) as (qf & q' & EL & Hret & EV & ->).
  destruct (s5_loop n enc _ qf Hb Hlen' ltac:(lia) EL Hret) as (wf & Ewf & Hfin).
  pose proof (s5_call n enc wf qf Ewf Hfin Hret) as Hs.
  destruct (rt_leave (RI.inf_ctx (rt_args enc n)) wf qf Hfin Hret) as [Hob _].
  rewrite EV in Hob. cbn [fst] in Hob.
  destruct (ZAC.zic_inflate enc ZApiInst.zi_init n true) as [[[is' cons] out] rc].
  cbv beta iota in Hs |- *. destruct Hs as (Hout & Hrc & Htot).
  destruct Hfin as [Hrel _].
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hput & _ & Hp0 & _ & _ & Harr & _).
  split; [|split].
  - rewrite Hout, (arr_rel_slice _ _ 0 (IS.ir_put (IS.w_r wf)) 0 (IS.ir_put (IS.w_r wf)) Harr) by lia.
    rewrite Hob. unfold RI.ob_slice. rewrite Hput. reflexivity.
  - exact Hrc.
  - rewrite Htot, Hout, arr_slice_length. lia.
Qed.
