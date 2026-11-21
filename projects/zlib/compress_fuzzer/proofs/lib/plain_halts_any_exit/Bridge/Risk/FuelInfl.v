(** * Bridge.Risk.FuelInfl — fuel sufficiency for S5's main inflate loop (group R).

    S5's own safety proof carries, through every trip of the inflate loop,
    the invariant [RefInflateSafeD.WINV] and a measure [PHI] (64 per unread
    input byte + 8 per output slot + 8 per buffered bit + a mode rank) that
    every continuing trip strictly lowers ([RefInflateSafeS1.dispatch_safe]),
    and it shows [PHI] starts below the loop's fuel
    [64 * (avail_in + avail_out + 64)] at the loop's entry
    ([RefInflateEqS.WINV_entry']).  So, from any state with [WINV] and
    [PHI] below the fuel, adding fuel changes nothing.

    [inf_loop_n_r] and [inf_loop_fuel_r] are [IFuelInfl.inf_loop_n] and
    [IFuelInfl.inf_loop_fuel] verbatim, so [IFuelInfl] can re-export
    [fuel_inf_loop_r] by [exact] once its precondition carries [WINV] and the
    [PHI] bound. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD RefInflateSafeS1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition inf_loop_n_r (iv : ivariant) (flush : Z) (n : Z) (w : iw) : istop * iw :=
  iterZ n
    (fun w => match dispatch iv flush w with
              | ARun _ w' => inl w'
              | ALeave w' => inr (SLeave, w')
              | ARet rc w' => inr (SRet rc, w')
              end)
    (fun w => (SLeave, w)) w.

Definition inf_loop_fuel_r (w : iw) : Z := 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64).

Lemma inf_loop_fuel_aux : forall m flush w F n, WINV w -> PHI w < F -> F <= Z.of_nat m -> 0 <= n ->
  inf_loop_n_r ivar_ref flush (F + n) w = inf_loop_n_r ivar_ref flush F w.
Proof.
  induction m as [|m IH]; intros flush w F n HW HP HF Hn.
  { pose proof (PHI_nonneg w HW). cbn [Z.of_nat] in HF. lia. }
  pose proof (PHI_nonneg w HW) as H0.
  unfold inf_loop_n_r. rewrite (iterZ_step (F + n)) by lia. rewrite (iterZ_step F) by lia.
  destruct w as [s c r].
  pose proof (dispatch_safe flush (mkW s c r) s c r HW (Z.le_refl _)) as D.
  destruct (dispatch ivar_ref flush (mkW s c r)) as [u w'|w'|rc w']; [| reflexivity | reflexivity].
  destruct D as [HW' HP'].
  replace (F + n - 1) with ((F - 1) + n) by lia.
  exact (IH flush w' (F - 1) n HW' ltac:(lia) ltac:(lia) Hn).
Qed.

(** The fuel statement, with S5's loop invariant and the [PHI] bound as the
    precondition. *)
Theorem fuel_inf_loop_r : forall flush w n,
  WINV w -> PHI w < inf_loop_fuel_r w -> 0 <= n ->
  inf_loop_n_r ivar_ref flush (inf_loop_fuel_r w + n) w = inf_loop_n_r ivar_ref flush (inf_loop_fuel_r w) w.
Proof.
  intros flush w n HW HP Hn. pose proof (PHI_nonneg w HW).
  apply (inf_loop_fuel_aux (Z.to_nat (inf_loop_fuel_r w))); [exact HW | exact HP | lia | exact Hn].
Qed.
