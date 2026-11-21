(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateArmLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateOkb.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateA_DIST1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition lf_w (s : inflate_state) (c : icall) (r : iregs) : iw := LOAD (inflate_fast (RESTORE (mkW s c r))).
Definition lf_res (s : inflate_state) (c : icall) (r : iregs) : ares unit :=
  let w := lf_w s c r in
  if is_mode (w_s w) =? TYPE then ARun tt (mkW (iset_back (w_s w) (-1)) (w_c w) (w_r w)) else ARun tt w.

(* zlib 1.4: the fast path also needs bits < 8 (inflate.c l.924) *)
Lemma arm_LEN_fast : forall s c r, 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  arm_LEN ivar_ref (mkW s c r) = lf_res s c r.
Proof.
  intros s c r Hh Hl Hb. unfold arm_LEN. mstep1 (@gr_eq iregs).
  cbn [iv_fast ivar_ref andb].
  rewrite (proj2 (Z.leb_le _ _) Hh), (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hb). cbn [andb].
  unfold lf_res, lf_w. rewrite abind_run. unfold amodify at 1.
  destruct (LOAD (inflate_fast (RESTORE (mkW s c r)))) as [s3 c3 r3] eqn:E3.
  mstep1 (@gs_eq inflate_state). cbn [w_s w_c w_r].
  destruct (is_mode s3 =? TYPE); [| rewrite aret_eq; reflexivity].
  unfold set_back, aux. cbn [iv_aux ivar_ref]. rewrite us_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition len_tail (c : icall) (here : Z) (r : iregs) (sb : inflate_state) : ares unit :=
  let r' := ddrop r (code_bits here) in
  let s' := iset_length (addback sb (code_bits here)) (code_val here) in
  if code_op here =? 0 then ARun tt (mkW (iset_mode s' LIT) c r')
  else if negb (Z.land (code_op here) 32 =? 0) then ARun tt (mkW (iset_mode (iset_back s' (-1)) TYPE) c r')
  else if negb (Z.land (code_op here) 64 =? 0) then ARun tt (mkW (iset_mode s' BAD) (icset_msg c MSG_invalid_literal_length_code) r')
  else arm_LENEXT ivar_ref (mkW (iset_mode (iset_extra s' (Z.land (code_op here) 15)) LENEXT) c r').

Lemma arm_LEN_slow : forall s c r, (ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) ->
  arm_LEN ivar_ref (mkW s c r) =
    let s0 := iset_back s 0 in
    match DECODE1 (is_lencode s) (is_lenbits s) (mkW s0 c r) with
    | ARun last (mkW _ _ r1) =>
        if negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0) then
          match DECODE2 (is_lencode s) last (mkW s0 c r1) with
          | ARun here (mkW _ _ r2) => len_tail c here (ddrop r2 (code_bits last)) (addback s0 (code_bits last))
          | ALeave w => ALeave w
          | ARet rc w => ARet rc w
          end
        else len_tail c last r1 s0
    | ALeave w => ALeave w
    | ARet rc w => ARet rc w
    end.
Proof.
  intros s c r Hslow. unfold arm_LEN. mstep1 (@gr_eq iregs).
  cbn [iv_fast ivar_ref].
  replace (true && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false
    by (symmetry; destruct Hslow as [H|[H|H]];
        [ rewrite (proj2 (Z.leb_gt _ _) H); reflexivity
        | rewrite (proj2 (Z.leb_gt 258 _) H); destruct (6 <=? ir_have r); reflexivity
        | rewrite (proj2 (Z.ltb_ge _ _) H); destruct (6 <=? ir_have r), (258 <=? ir_left r); reflexivity ]).
  unfold set_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 (@gs_eq inflate_state).
  cbn [is_lencode is_lenbits iset_back]. cbv zeta. rewrite abind_run.
  destruct (DECODE1 (is_lencode s) (is_lenbits s) (mkW (iset_back s 0) c r)) as [last [s1 c1 r1] | w | rc w] eqn:H1; try reflexivity.
  destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H1) as [-> ->].
  rewrite abind_run.
  destruct (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)).
  - rewrite abind_run.
    destruct (DECODE2 (is_lencode s) last (mkW (iset_back s 0) c r1)) as [here [s2 c2 r2] | w | rc w] eqn:H2; try reflexivity.
    destruct (DECODE_k_run _ _ _ _ _ _ _ _ _ _ _ H2) as [-> ->].
    mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. rewrite aret_eq. cbv beta iota.
    mstep1 DROPBITS_eq. mstep1 us_eq. mstep1 us_eq. unfold len_tail, ddrop, addback. cbn [ir_hold ir_bits irset_bits irset_hold is_back iset_back].
    destruct (code_op here =? 0); [rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op here) 32 =? 0)); [mstep1 us_eq; rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op here) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
  - rewrite aret_eq. cbv beta iota. mstep1 DROPBITS_eq. unfold add_back, aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 us_eq.
    unfold len_tail, ddrop, addback.
    destruct (code_op last =? 0); [rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op last) 32 =? 0)); [mstep1 us_eq; rewrite set_mode_eq; reflexivity|].
    destruct (negb (Z.land (code_op last) 64 =? 0)); [rewrite go_bad_eq; reflexivity|].
    mstep1 us_eq. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_LEN__eq : forall s c r, arm_LEN_ ivar_ref (mkW s c r) = arm_LEN ivar_ref (mkW (iset_mode s LEN) c r).
Proof. intros. unfold arm_LEN_. mstep1 set_mode_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma len_okb_fast : forall s c r, len_okb (mkW s c r) = true -> 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  0 <= is_lenbits s <= 15 /\ 0 <= is_distbits s <= 15 /\ lenfast_okb (mkW s c r) = true.
Proof.
  intros s c r H Hh Hl Hb. unfold len_okb in H. cbn [w_s w_r w_c] in H.
  rewrite (proj2 (Z.leb_le _ _) Hh), (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hb) in H. cbn [andb] in H.
  destruct (Z.leb_spec 0 (is_lenbits s)); [| discriminate H]. destruct (Z.leb_spec (is_lenbits s) 15); [| discriminate H].
  destruct (Z.leb_spec 0 (is_distbits s)); [| discriminate H]. destruct (Z.leb_spec (is_distbits s) 15); [| discriminate H].
  cbn [andb] in H. repeat split; try assumption.
Qed.

(* [comment removed for export] *)
Lemma lenfast_okb_sound : forall s c r, lenfast_okb (mkW s c r) = true ->
  let wR := RESTORE (mkW s c r) in
  ff_ok (w_s wR) (w_c wR) (w_r wR) = true
  /\ let c1 := w_c (inflate_fast wR) in
     0 <= ic_next_in c1 /\ 0 <= ic_avail_in c1 /\ ic_next_in c1 + ic_avail_in c1 = arr_len (ic_input c)
     /\ 0 <= ic_next_out c1 /\ 0 <= ic_avail_out c1 /\ ic_next_out c1 + ic_avail_out c1 = arr_len (ic_outbuf c).
Proof.
  intros s c r H. unfold lenfast_okb in H. cbn [w_c] in H. cbv zeta.
  destruct (ff_ok _ _ _); [| discriminate H]. cbn [andb] in H.
  repeat match type of H with (?a && ?b) = true => apply andb_prop in H; destruct H as [H ?X] end.
  repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X end.
  repeat split; assumption.
Qed.

