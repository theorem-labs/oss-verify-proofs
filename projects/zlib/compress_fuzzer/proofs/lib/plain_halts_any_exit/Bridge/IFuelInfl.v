(** * Bridge.IFuelInfl — INTERFACE (part C lead): fuel sufficiency for S5's inflate loops.

    S5's two inflate loops run [iterZ] with a fuel computed from the call's
    buffer sizes and, when it runs out, LEAVE as if the loop had ended
    normally.  RT's loops fail ([None]/[InfFuel]) instead, and RT's main-loop
    fuel ([Inflate.inf_fuel]) is LARGER than S5's, so RT finishing does not
    by itself show S5 finishes.  Each loop is restated below with its fuel as
    a parameter ([inf_loop_n], [inflate_fast_n]); the restatement is checked
    equal to S5's own definition by [reflexivity], and the fuel statement
    says adding fuel changes nothing.

    The precondition is S5's own loop invariant and measure (see
    [fuel_inf_loop]).  The inner fuels of [inflate_fast]'s decode
    ([dolen]/[dodist], fuel 4), [inflate_table] and the CODELENS loop are
    internal to pairs I9, I15, I16 and are stated in the inflate group's own
    files against the table invariant it defines.

    [fuel_inf_loop] is proved by the risk group (group R) in
    [Risk/FuelInfl.v], which restates [inf_loop_n] / [inf_loop_fuel]
    verbatim and does not import this file; it is re-exported here. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require FuelInfl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** RT's own run from [q] ends by leaving or returning, within RT's fuel.
    (No longer a premise of [fuel_inf_loop]; kept for [Risk/FuelInflCheck.v].) *)
Definition rt_completes (c : RI.InfCtx) (q : RI.InfSt) : Prop :=
  exists r, RI.inf_loop (RI.inf_fuel q) c q = Some r
            /\ (exists q', r = RI.InfLeave q' \/ exists rc, r = RI.InfRet q' rc).

(** The call context: same flush, and the window allocation succeeds (the
    harness's oracle answers [wans true]). *)
Definition ctx_rel (flush : Z) (c : RI.InfCtx) : Prop :=
  RI.n_flush c = flush /\ RI.n_walloc c = true.

(* ------------------------------------------------------------------------- *)
(* The main loop                                                             *)
(* ------------------------------------------------------------------------- *)

Definition inf_loop_n (iv : ivariant) (flush : Z) (n : Z) (w : iw) : istop * iw :=
  iterZ n
    (fun w => match dispatch iv flush w with
              | ARun _ w' => inl w'
              | ALeave w' => inr (SLeave, w')
              | ARet rc w' => inr (SRet rc, w')
              end)
    (fun w => (SLeave, w)) w.

Definition inf_loop_fuel (w : iw) : Z := 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64).

Lemma inf_loop_n_eq : forall iv flush w, inf_loop iv flush w = inf_loop_n iv flush (inf_loop_fuel w) w.
Proof. reflexivity. Qed.

(** The precondition is S5's own loop invariant [RefInflateSafeD.WINV] and
    its measure [RefInflateSafeD.PHI] (64 have + 8 bits + 8 left + mode
    rank, lowered by every continuing trip: S5's [dispatch_safe]) below the
    fuel.  The first version asked for [iw_rel] and [rt_completes] instead,
    which do not give [WINV].  At the loop's entry
    both facts are S5's [RefInflateEqS.WINV_entry'] for [W0 st zc]
    ([RefInflate_runA.inflate_m_W0]), from [INV st] ([ZApiOk.INV_is0] for
    the harness's fresh state) and [ZC zc]. *)
Lemma fuel_inf_loop : forall flush w n,
  RefInflateSafeD.WINV w -> RefInflateSafeD.PHI w < inf_loop_fuel w -> 0 <= n ->
  inf_loop_n ivar_ref flush (inf_loop_fuel w + n) w = inf_loop_n ivar_ref flush (inf_loop_fuel w) w.
Proof. exact OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk.FuelInfl.fuel_inf_loop_r. Qed.

(* ------------------------------------------------------------------------- *)
(* inflate_fast's loop                                                       *)
(* ------------------------------------------------------------------------- *)

(** [InflateFast.inflate_fast] with its trip fuel as a parameter; the body is
    S5's, verbatim. *)
Definition inflate_fast_n (n : Z) (w : iw) : iw :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  let in_ := ic_next_in c in
  let last := in_ + wrap32 (ic_avail_in c - 5) in
  let out := ic_next_out c in
  let beg := out - wrap32 (ir_out r - ic_avail_out c) in
  let end_ := out + wrap32 (ic_avail_out c - 257) in
  let x := mkFX (ic_input c) last beg end_ (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
                (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s) in
  let f0 := mkF in_ out (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c) in
  let '(f, mm) :=
    iterZ n
      (fun f => match fast_trip x s f with
                | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f'
                              else inr (f', None)
                | FBreak f' mode msg => inr (f', Some (mode, msg))
                end)
      (fun f => (f, None)) f0 in
  let len := Z.shiftr (f_bits f) 3 in
  let f := fset_in f (f_in f - len) in
  let f := fset_bits f (wrap32 (f_bits f - Z.shiftl len 3)) in
  let f := fset_hold f (Z.land (f_hold f) (zmask (f_bits f))) in
  let c := icset_outbuf c (f_ob f) in
  let c := icset_next_in c (f_in f) in
  let c := icset_next_out c (f_out f) in
  let c := icset_avail_in c (wrap32 (if f_in f <? x_last x then 5 + (x_last x - f_in f) else 5 - (f_in f - x_last x))) in
  let c := icset_avail_out c (wrap32 (if f_out f <? x_end x then 257 + (x_end x - f_out f) else 257 - (f_out f - x_end x))) in
  let s := iset_hold s (f_hold f) in
  let s := iset_bits s (f_bits f) in
  let '(s, c) := match mm with
                 | Some (mode, Some msg) => (iset_mode s mode, icset_msg c msg)
                 | Some (mode, None) => (iset_mode s mode, c)
                 | None => (s, c)
                 end in
  mkW s c r.

Definition inflate_fast_fuel (w : iw) : Z := 8 * ic_avail_in (w_c w) + ic_avail_out (w_c w) + 80.

(** No fuel statement for this loop: RT's [InflateFast.if_model] runs with
    fuel [S (end - out)] = [avail_out - 256], below [inflate_fast_fuel], so a
    lockstep proof for every fuel at least RT's trip count, instantiated at
    [inflate_fast_fuel] through this equation, covers it (group I's
    [Infl/IFast.v]).  The [fuel_inflate_fast] of the first version was
    removed on 2026-10-20: its [rt_completes] premise is not available
    inside a one-trip lemma. *)
Lemma inflate_fast_n_eq : forall w, inflate_fast w = inflate_fast_n (inflate_fast_fuel w) w.
Proof. reflexivity. Qed.
