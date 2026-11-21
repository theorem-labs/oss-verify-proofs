(** * Bridge.Infl.IFastLoop — pair I16: [inflate_fast]'s loop, S5 vs RT, in lockstep.

    One RT [if_loop] trip against one S5 [iterZ] trip ([IFastTrip.ft_trip]), by induction
    on RT's fuel; S5's fuel only has to be at least RT's.  When RT's loop leaves with the
    guard failing ([IfStop]) or at an end of block ([IfEob]), S5's loop leaves at the same
    state with no mode change / with TYPE.  RT's other exits ([IfBad], [IfFuel], [None])
    need no match.

    The exit bounds are what the epilogue needs: the bit position [Q] never moves back and
    ends at most at [8 * (last + 5)] (the input's end), and [out] ends at most at [N] (the
    output buffer's end). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IFastKit IFastTrip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** S5's loop step, verbatim from [inflate_fast]. *)
Definition stepS (x : IF.ffx) (s : IS.inflate_state) : IF.ffs -> IF.ffs + (IF.ffs * option (Z * option Z)) :=
  fun f => match IF.fast_trip x s f with
           | IF.FCont f' => if (IF.f_in f' <? IF.x_last x) && (IF.f_out f' <? IF.x_end x) then inl f'
                            else inr (f', None)
           | IF.FBreak f' mode msg => inr (f', Some (mode, msg))
           end.

Lemma fl_stepS : forall x s f, stepS x s f
  = match IF.fast_trip x s f with
    | IF.FCont f' => if (IF.f_in f' <? IF.x_last x) && (IF.f_out f' <? IF.x_end x) then inl f'
                     else inr (f', None)
    | IF.FBreak f' mode msg => inr (f', Some (mode, msg))
    end.
Proof. reflexivity. Qed.

Section Loop.
Variables (x : IF.ffx) (c : RIF.IfCtx) (sS : IS.inflate_state) (N : Z).
Hypothesis X : xrel x c sS N.

Lemma fl_loop : forall k f s n r, frel N f s -> rng s -> RIF.f_in s < RIF.f_last c -> RIF.f_out s < RIF.f_end c ->
  Z.of_nat k <= n -> RIF.if_loop k c s = Some r ->
  match r with
  | RIF.IfStop s' => exists f', iterZ n (stepS x sS) (fun f => (f, None)) f = (f', None)
       /\ frel N f' s' /\ rng s' /\ Q s <= Q s' <= 8 * (RIF.f_last c + 5) /\ RIF.f_out s <= RIF.f_out s' <= N
  | RIF.IfEob s' => exists f', iterZ n (stepS x sS) (fun f => (f, None)) f = (f', Some (IS.TYPE, None))
       /\ frel N f' s' /\ rng s' /\ Q s <= Q s' <= 8 * (RIF.f_last c + 5) /\ RIF.f_out s <= RIF.f_out s' <= N
  | _ => True end.
Proof.
  induction k as [|k IH]; intros f s n r F R Hin Hout Hn Hl; [discriminate Hl|].
  pose proof (xr_N _ _ _ _ X) as HN. pose proof (rg_bits _ R) as Rb.
  assert (HQ : Q s <= 8 * (RIF.f_last c - 1)) by (unfold Q; lia).
  rewrite RIF.if_loop_S, RIF.if_step_unfold in Hl.
  rewrite iterZ_step by lia. rewrite fl_stepS.
  pose proof (ft_trip x c sS N X f s F R ltac:(lia)) as T.
  destruct (RIF.if_body c s) as [s1|s1|s1 m|].
  - destruct T as (f1 & Hf1 & F1 & R1 & Q1 & O1). rewrite Hf1.
    rewrite (fr_in _ _ _ F1), (fr_out _ _ _ F1), (xr_last _ _ _ _ X), (xr_end _ _ _ _ X).
    unfold RIF.if_guard in Hl.
    destruct (Z.ltb_spec (RIF.f_in s1) (RIF.f_last c)) as [G1|G1];
      destruct (Z.ltb_spec (RIF.f_out s1) (RIF.f_end c)) as [G2|G2]; cbn [andb] in Hl |- *.
    + pose proof (IH f1 s1 (n - 1) r F1 R1 G1 G2 ltac:(lia) Hl) as T.
      destruct r as [s'|s'|s'|s' m'|]; try exact I;
        destruct T as (f' & Hf' & F' & R' & Q' & O'); exists f'; conjs; first [exact Hf' | exact F' | exact R' | lia].
    + injection Hl as <-. exists f1. conjs; first [reflexivity | exact F1 | exact R1 | lia].
    + injection Hl as <-. exists f1. conjs; first [reflexivity | exact F1 | exact R1 | lia].
    + injection Hl as <-. exists f1. conjs; first [reflexivity | exact F1 | exact R1 | lia].
  - destruct T as (f1 & Hf1 & F1 & R1 & Q1 & O1). rewrite Hf1.
    injection Hl as <-. exists f1. conjs; first [reflexivity | exact F1 | exact R1 | lia].
  - injection Hl as <-. exact I.
  - injection Hl as <-. exact I.
Qed.

End Loop.
