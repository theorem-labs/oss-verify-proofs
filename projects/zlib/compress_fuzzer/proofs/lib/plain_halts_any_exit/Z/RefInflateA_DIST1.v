(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateLoop.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateArmLib3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_HCRC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_NAME.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_EXTRA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateA_DISTEXT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma DECODE_k_O : forall p index need s c r,
  DECODE_k 0 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof. intros. reflexivity. Qed.

Lemma DECODE_k_S : forall k p index need s c r,
  DECODE_k (S k) p index need (mkW s c r)
  = let here := code_at s p (index (ir_hold r)) in
    if need here <=? ir_bits r then ARun here (mkW s c r)
    else if ir_have r =? 0 then ALeave (mkW s c r) else DECODE_k k p index need (mkW s c (pullr c r)).
Proof.
  intros.
  change (DECODE_k (S k) p index need (mkW s c r))
    with (abind HOLD (fun hold => abind (gr ir_bits) (fun bits => abind (gs (fun s0 => code_at s0 p (index hold))) (fun here =>
            if need here <=? bits then aret here else abind PULLBYTE (fun _ => DECODE_k k p index need)))) (mkW s c r)).
  unfold abind at 1. rewrite HOLD_eq. unfold abind at 1. cbn [gr w_r]. unfold abind at 1. cbn [gs w_s]. cbv zeta.
  destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [reflexivity|].
  unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity.
Qed.

Lemma dchk_sound : forall k s c p index need r r',
  dchk k c index need (ctab_size p) (code_at s p) r = Some r' ->
  let here := code_at s p (index (ir_hold r')) in
  0 <= index (ir_hold r') < ctab_size p /\ 0 <= need here <= 32
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r
  /\ (need here <= ir_bits r' -> DECODE_k k p index need (mkW s c r) = ARun here (mkW s c r'))
  /\ (ir_bits r' < need here -> ir_have r' = 0 /\ DECODE_k k p index need (mkW s c r) = ALeave (mkW s c r')).
Proof.
  induction k as [|k IH]; intros s c p index need r r' H; cbn [dchk] in H; cbv zeta;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? ctab_size p) && (0 <=? need (code_at s p (index (ir_hold r)))) && (need (code_at s p (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.leb_le in H4.
  - destruct (Z.leb_spec (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [Hb|Hb]; [| discriminate H].
    injection H as <-.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
    all: intros X; first [rewrite DECODE_k_O; reflexivity | exfalso; lia].
  - rewrite DECODE_k_S. cbv zeta.
    destruct (Z.leb_spec (need (code_at s p (index (ir_hold r)))) (ir_bits r)) as [Hb|Hb].
    + injection H as <-. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
      all: intros X; first [reflexivity | exfalso; lia].
    + destruct (Z.eqb_spec (ir_have r) 0) as [Hh|Hh].
      * injection H as <-. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
        all: intros X; first [reflexivity | exfalso; lia | split; [exact Hh | reflexivity]].
      * exact (IH s c p index need (pullr c r) r' H).
Qed.

Definition dist_tail (c : icall) (here : Z) (r : iregs) (sb : inflate_state) : ares unit :=
  let r' := ddrop r (code_bits here) in
  let s' := addback sb (code_bits here) in
  if negb (Z.land (code_op here) 64 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_invalid_distance_code) r')
  else arm_DISTEXT ivar_ref (mkW (iset_mode (iset_extra (iset_offset s' (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c r').

Lemma DECODE_k_run : forall k p index need s c r h s1 c1 r1,
  DECODE_k k p index need (mkW s c r) = ARun h (mkW s1 c1 r1) -> s1 = s /\ c1 = c.
Proof.
  induction k as [|k IH]; intros p index need s c r h s1 c1 r1 H.
  - rewrite DECODE_k_O in H. injection H as _ <- <-. split; reflexivity.
  - rewrite DECODE_k_S in H. cbv zeta in H.
    destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); [injection H as _ <- <-; split; reflexivity|].
    destruct (ir_have r =? 0); [discriminate H|]. exact (IH _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma arm_DIST_eq : forall s c r,
  arm_DIST ivar_ref (mkW s c r) =
    match DECODE1 (is_distcode s) (is_distbits s) (mkW s c r) with
    | ARun last (mkW _ _ r1) =>
        if Z.land (code_op last) 240 =? 0 then
          match DECODE2 (is_distcode s) last (mkW s c r1) with
          | ARun here (mkW _ _ r2) => dist_tail c here (ddrop r2 (code_bits last)) (addback s (code_bits last))
          | ALeave w => ALeave w
          | ARet rc w => ARet rc w
          end
        else dist_tail c last r1 s
    | ALeave w => ALeave w
    | ARet rc w => ARet rc w
    end.
Proof.
  intros s c r. unfold arm_DIST. mstep1 (@gs_eq inflate_state). rewrite abind_run.
  destruct (DECODE1 (is_distcode s) (is_distbits s) (mkW s c r)) as [last [s1 c1 r1] | w | rc w] eqn:H1; try reflexivity.
  destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H1) as [-> ->].
  rewrite abind_run.
  destruct (Z.land (code_op last) 240 =? 0).
  - rewrite abind_run.
    destruct (DECODE2 (is_distcode s) last (mkW s c r1)) as [here [s2 c2 r2] | w | rc w] eqn:H2; try reflexivity.
    destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H2) as [-> ->].
    mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. rewrite aret_eq. cbv beta iota.
    mstep1 DROPBITS_eq. mstep1 us_eq. unfold dist_tail, ddrop, addback. cbn [ir_hold ir_bits irset_bits irset_hold is_back iset_back].
    destruct (negb (Z.land (code_op here) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
  - rewrite aret_eq. cbv beta iota. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq.
    unfold dist_tail, ddrop, addback.
    destruct (negb (Z.land (code_op last) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.
Ltac inl_tac := cbn; repeat (first [left; reflexivity | right]).

Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_land by lia. apply Z.land_ones. lia. Qed.

Lemma dchk_step : forall k c index need N tab r r',
  dchk k c index need N tab r = Some r' -> ir_bits r < need (tab (index (ir_hold r))) ->
  0 <= index (ir_hold r) < N /\ need (tab (index (ir_hold r))) <= 32
  /\ match k with
     | O => False
     | S k' => (ir_have r = 0 /\ r' = r) \/ (ir_have r <> 0 /\ dchk k' c index need N tab (pullr c r) = Some r')
     end.
Proof.
  intros k c index need N tab r r' H Hb.
  destruct k as [|k']; cbn [dchk] in H;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? N) && (0 <=? need (tab (index (ir_hold r)))) && (need (tab (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.leb_le in H4;
    rewrite (proj2 (Z.leb_gt _ _) Hb) in H.
  - discriminate H.
  - split; [lia|]. split; [exact H4|].
    destruct (Z.eqb_spec (ir_have r) 0) as [Hh|Hh]; [left; split; [exact Hh | congruence] | right; split; [exact Hh | exact H]].
Qed.

Lemma dchk_found : forall k c index need N tab r r',
  dchk k c index need N tab r = Some r' -> need (tab (index (ir_hold r))) <= ir_bits r ->
  0 <= index (ir_hold r) < N /\ r' = r.
Proof.
  intros k c index need N tab r r' H Hb.
  destruct k as [|k']; cbn [dchk] in H;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? N) && (0 <=? need (tab (index (ir_hold r)))) && (need (tab (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2;
    rewrite (proj2 (Z.leb_le _ _) Hb) in H.
  - injection H as <-. split; [lia | reflexivity].
  - injection H as <-. split; [lia | reflexivity].
Qed.
Definition dtab (s : inflate_state) : Z -> Z := code_at s (is_distcode s).
Definition dN (s : inflate_state) : Z := ctab_len (is_distcode s).

Lemma ctab_size_len : forall p, ctab_size p = ctab_len p.
Proof. intros p. destruct p; reflexivity. Qed.

Section ArmDIST1.
End ArmDIST1.
