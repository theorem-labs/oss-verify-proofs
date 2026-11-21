(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import
  ZIface InflateState Inftrees ModelRel InftreesCoverage ItableModel ItCovIface ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import ItAPure ItBridgeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition trng (a : arr) : Prop := forall i, 0 <= i < 1444 -> 0 <= arr_get a i < 4294967296.

Lemma trng_set : forall a k v, trng a -> 0 <= v < 4294967296 -> trng (arr_set a k v).
Proof.
  intros a k v H Hv i Hi. rewrite arr_get_set. destruct ((k =? i) && arr_inb a k); [exact Hv| apply H; exact Hi].
Qed.
Lemma trng_pack : forall a k op b v, trng a -> trng (arr_set a k (code_pack op b v)).
Proof. intros. apply trng_set; [assumption|]. pose proof (code_pack_range op b v) as R. change (2 ^ 32) with 4294967296 in R. exact R. Qed.

Lemma loopZ_inv : forall {A} (P : A -> Prop) (step : A -> bool * A),
  (forall a, P a -> P (snd (step a))) -> forall n a, P a -> P (loopZ n step a).
Proof.
  intros A P step HS n. remember (Z.to_nat n) as k eqn:Ek. revert n Ek.
  induction k as [|k IH]; intros n Ek a Ha.
  - rewrite loopZ_le0 by lia. exact Ha.
  - rewrite loopZ_step by lia. pose proof (HS a Ha) as Hs. destruct (step a) as [c a']. cbn [snd] in Hs.
    destruct c; [apply IH; [lia| exact Hs]| exact Hs].
Qed.

Lemma it_fill_trng : forall here incr huff drop next fill tbl,
  0 <= here < 4294967296 -> trng tbl -> trng (it_fill here incr huff drop next fill tbl).
Proof.
  intros here incr huff drop next fill tbl Hh Ht. unfold it_fill.
  apply (loopZ_inv (fun ft : Z * arr => trng (snd ft))); [| exact Ht].
  intros [f t] Hft. cbn [snd] in *. destruct (negb (wrap32 (f - incr) =? 0)); cbn [snd]; apply trng_set; assumption.
Qed.

Definition stP (w : arr) (st : ItSt) : Prop := trng (t_tbl st) /\ t_work st = w.
Lemma it_step_inv : forall x w st, stP w st ->
  match it_step x st with ItCont s => stP w s | ItBreak s => stP w s | ItFail s => stP w s end.
Proof.
  intros x w st [HT HW]. unfold it_step.
  destruct (if arr_get (t_work st) (t_sym st) + 1 <? it_match (x_ty x) then (0, arr_get (t_work st) (t_sym st))
            else if it_match (x_ty x) <=? arr_get (t_work st) (t_sym st)
                 then (wrap8 (it_extra (x_ty x) (t_work st) (arr_get (t_work st) (t_sym st) - it_match (x_ty x))),
                       it_base (x_ty x) (t_work st) (arr_get (t_work st) (t_sym st) - it_match (x_ty x)))
                 else (96, 0)) as [ho hv].
  assert (HF : forall incr fill, trng (it_fill (code_pack ho (wrap8 (t_len st - t_drop st)) hv) incr (t_huff st) (t_drop st) (t_next st) fill (t_tbl st))).
  { intros incr fill. apply it_fill_trng; [| exact HT]. pose proof (code_pack_range ho (wrap8 (t_len st - t_drop st)) hv) as R.
    change (2 ^ 32) with 4294967296 in R. exact R. }
  cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] =>
    lazymatch c with
    | andb _ _ => destruct c eqn:?
    | it_not_enough _ _ => destruct c eqn:?
    end end; unfold stP; cbn [t_tbl t_work]; (split; [| exact HW]); first [apply HF | apply trng_pack; apply HF].
Qed.

Lemma iterZ_it_inv : forall x w n st, stP w st ->
  match iterZ n (fun st => match it_step x st with ItCont st' => inl st' | ItBreak st' => inr (inl st') | ItFail st' => inr (inr st') end)
               (fun st => inl st) st with
  | inl s => stP w s | inr s => stP w s end.
Proof.
  intros x w n. remember (Z.to_nat n) as k eqn:Ek. revert n Ek.
  induction k as [|k IH]; intros n Ek st Hst.
  - rewrite iterZ_le0 by lia. exact Hst.
  - rewrite iterZ_step by lia. pose proof (it_step_inv x w st Hst) as HS.
    destruct (it_step x st) as [s|s|s]; [apply IH; [lia| exact HS]| exact HS| exact HS].
Qed.

Section Res.
  Variables (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z).
  Hypothesis C : itc ty lf lens_ofs codes nx bits cf wf.

  Lemma tblA_trng : trng (tblA cf).
  Proof. intros i Hi. rewrite tblA_get. apply (C_cf _ _ _ _ _ _ _ _ C). unfold N_CODES. exact Hi. Qed.

  Lemma w1_range : forall i, 0 <= i < 288 -> 0 <= arr_get (work1A lf lens_ofs codes wf) i < 65536.
  Proof.
    intros j Hj. unfold work1A. rewrite itm_work_eq.
    apply (sort_k_work_range (lensA lf) lens_ofs codes (offsA lf lens_ofs codes) (workA wf) 288); [|exact Hj].
    intros i Hi. rewrite workA_get. apply (C_wf _ _ _ _ _ _ _ _ C). unfold N_WORK. exact Hi.
  Qed.

  Theorem resA_ranges :
    (forall i, 0 <= i < 1444 -> 0 <= arr_get (it_tbl (resA ty lf lens_ofs codes nx bits cf wf)) i < 4294967296)
    /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work (resA ty lf lens_ofs codes nx bits cf wf)) i < 65536).
  Proof.
    rewrite (res_phases ty lf lens_ofs codes nx bits cf wf).
    pose proof tblA_trng as HT. pose proof w1_range as HW1.
    assert (HW0 : forall i, 0 <= i < 288 -> 0 <= arr_get (workA wf) i < 65536).
    { intros i Hi. rewrite workA_get. apply (C_wf _ _ _ _ _ _ _ _ C). unfold N_WORK. exact Hi. }
    destruct (mxA lf lens_ofs codes =? 0); [unfold it_tbl, it_work; cbn [fst snd]; split; [apply trng_pack, trng_pack, HT| exact HW0]|].
    destruct (itm_reject _ _ _); [unfold it_tbl, it_work; cbn [fst snd]; split; [exact HT| exact HW0]|].
    destruct (it_not_enough _ _); [unfold it_tbl, it_work; cbn [fst snd]; split; [exact HT| exact HW1]|].
    match goal with |- context [it_loop ?x ?c ?s0] =>
      pose proof (iterZ_it_inv x (work1A lf lens_ofs codes wf) (c + 1) s0) as HL; fold (it_loop x c s0) in HL;
      destruct (it_loop x c s0) as [s|s] end.
    - destruct HL as [HLt HLw]; [split; [exact HT| reflexivity]|].
      unfold it_tbl, it_work; cbn [fst snd]. rewrite HLw. split; [| exact HW1].
      destruct (negb (t_huff s =? 0)); [apply trng_pack, HLt| exact HLt].
    - destruct HL as [HLt HLw]; [split; [exact HT| reflexivity]|].
      unfold it_tbl, it_work; cbn [fst snd]. rewrite HLw. split; [exact HLt| exact HW1].
  Qed.
End Res.
