(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition arm_safe (M : Z) (arm : AM unit) : Prop :=
  forall w0 s c r, WINV (mkW s c r) -> is_mode s = M -> PHI (mkW s c r) <= PHI w0 -> POST w0 (arm (mkW s c r)).


Lemma CORE_keep : forall s s', CORE s ->
  is_window_blk s' = is_window_blk s -> is_wsize s' = is_wsize s -> arr_len (is_window s') = arr_len (is_window s) ->
  is_wbits s' = is_wbits s -> is_whave s' = is_whave s -> is_wnext s' = is_wnext s -> is_wrap s' = is_wrap s ->
  arr_len (is_lens s') = arr_len (is_lens s) -> arr_len (is_work s') = arr_len (is_work s) -> arr_len (is_codes s') = arr_len (is_codes s) ->
  is_sane s' = is_sane s -> 0 <= is_length s' < 2 ^ 32 ->
  CORE s'.
Proof.
  intros s s' H E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 HL. unfold CORE in *.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11.
  destruct H as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14).
  repeat (split; [assumption|]). exact HL.
Qed.

Lemma mod_pow2_range : forall h n, 0 <= n -> 0 <= h mod 2 ^ n < 2 ^ n.
Proof. intros h n Hn. apply Z.mod_pos_bound. apply pow2_pos. exact Hn. Qed.

Lemma land_65535 : forall a, 0 <= Z.land a 65535 < 65536.
Proof. intros a. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma common_keep : forall s s', common s ->
  is_wbits s' = is_wbits s -> is_flags s' = is_flags s -> is_check s' = is_check s -> common s'.
Proof. intros s s' H E1 E2 E3. unfold common in *. rewrite E1, E2, E3. exact H. Qed.

Lemma common_update_check : forall s s0 s' bytes,
  common s -> is_wbits s' = is_wbits s -> is_flags s' = is_flags s -> is_flags s0 = is_flags s ->
  is_check s' = UPDATE_CHECK_bytes s0 (is_check s) bytes -> common s'.
Proof.
  intros s s0 s' bytes [W F] E1 E2 E0 E3. unfold common. rewrite E1, E2, E3. split; [exact W|].
  intros F0. unfold UPDATE_CHECK_bytes. rewrite E0, F0. cbn [Z.eqb negb]. unfold iadler32_upd. apply adler32_model_canon.
Qed.

Lemma tables_keep : forall s s', tables s ->
  is_codes s' = is_codes s -> is_lencode s' = is_lencode s -> is_distcode s' = is_distcode s ->
  is_lenbits s' = is_lenbits s -> is_distbits s' = is_distbits s -> tables s'.
Proof. intros s s' H E1 E2 E3 E4 E5. unfold tables in *. rewrite E1, E2, E3, E4, E5. exact H. Qed.

Lemma lneed_keep : forall s s' p root h,
  is_codes s' = is_codes s -> lneed s' p root h = lneed s p root h.
Proof. intros s s' p root h E. unfold lneed, code_at. rewrite E. reflexivity. Qed.

Lemma REGS_out : forall c r ob put left,
  REGS c r -> arr_len ob = arr_len (ic_outbuf c) -> 0 <= put -> 0 <= left -> put + left = arr_len (ic_outbuf c) ->
  REGS (icset_outbuf c ob) (irset_left (irset_put r put) left).
Proof.
  intros c r ob put left HR Hob Hp Hl Hpl. unfold REGS in *. destruct c, r; cbn in *.
  destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  rewrite Hob. repeat (split; [first [assumption | lia]|]). exact A10.
Qed.


Ltac winv_open HW E :=
  unfold WINV in HW; cbn [w_s w_c w_r] in HW; rewrite E in HW; mred_in HW;
  destruct HW as ((CW1 & CW2 & CW3 & CW4 & CW5 & CW6 & CW7 & CW8 & CW9 & CA1 & CA2 & CA3 & CS & CL)
                  & (RN & RH & RNH & RP & RL & RPL & [RB RHO] & RIN & RNI & RNO) & HMF & HWF & HWB).

Ltac winv_open2 HW E HC HR :=
  unfold WINV in HW; cbn [w_s w_c w_r] in HW; rewrite E in HW; mred_in HW;
  destruct HW as (HC & HR & HMF & HWF & HWB).

Ltac regs_open HR :=
  pose proof HR as HR_copy;
  destruct HR_copy as (RN & RH & RNH & RP & RL & RPL & [RB RHO] & RIN & RNI & RNO).

Ltac winv_split :=
  unfold WINV; cbn [w_s w_c w_r]; sacc; mred; sacc;
  split; [|split; [|split; [|split]]].

Ltac winv_splitE E :=
  unfold WINV; cbn [w_s w_c w_r]; sacc; rewrite E; mred; sacc;
  split; [|split; [|split; [|split]]].

Ltac core_keep HC := apply (CORE_keep _ _ HC); [sacc; rewrite ?arr_len_set; try reflexivity..|sacc].
Ltac common_keep HC := apply (common_keep _ _ HC); sacc; reflexivity.
Ltac tables_keep HT := apply (tables_keep _ _ HT); sacc; reflexivity.

Ltac phi_norm E HP :=
  lazymatch goal with
  | |- _ < PHI ?w0 => let P := fresh "PW0" in set (P := PHI w0) in *; clearbody P
  | |- _ <= PHI ?w0 => let P := fresh "PW0" in set (P := PHI w0) in *; clearbody P
  end;
  unfold PHI; cbn [w_s w_c w_r]; sacc; try rewrite E; mred;
  unfold PHI in HP; cbn [w_s w_c w_r] in HP; sacc_in HP; rewrite E in HP; mred_in HP.

Ltac phi_goal :=
  lazymatch goal with
  | |- _ < PHI ?w0 => let P := fresh "PW0" in set (P := PHI w0) in *; clearbody P
  | |- _ <= PHI ?w0 => let P := fresh "PW0" in set (P := PHI w0) in *; clearbody P
  end;
  unfold PHI; cbn [w_s w_c w_r]; sacc; mred.


Section Rules2.
  Context {A B : Type}.
  Lemma POST_bind_run : forall w0 (m : AM A) (f : A -> AM B) w a w',
    m w = ARun a w' -> POST w0 (f a w') -> POST w0 (abind m f w).
  Proof. intros w0 m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma POST_bind_leave : forall w0 (m : AM A) (f : A -> AM B) w w',
    m w = ALeave w' -> WINV w' -> POST w0 (abind m f w).
  Proof. intros w0 m f w w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma POST_bind_ret : forall w0 (m : AM A) (f : A -> AM B) w rc w',
    m w = ARet rc w' -> WINV w' /\ INV (w_s w') -> POST w0 (abind m f w).
  Proof. intros w0 m f w rc w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma abind_assoc : forall {C} (m : AM A) (f : A -> AM B) (g : B -> AM C) w,
    abind (abind m f) g w = abind m (fun x => abind (f x) g) w.
  Proof. intros C m f g w. unfold abind. destruct (m w); reflexivity. Qed.
  Lemma POST_arm : forall M arm w0 s c r,
    arm_safe M arm -> WINV (mkW s c r) -> is_mode s = M -> PHI (mkW s c r) <= PHI w0 -> POST w0 (arm (mkW s c r)).
  Proof. intros M arm w0 s c r H. exact (H w0 s c r). Qed.
End Rules2.

Ltac aflat := repeat rewrite abind_assoc.
Ltac acase H :=
  lazymatch goal with
  | |- POST _ (abind (if ?cnd then _ else _) _ _) => destruct cnd eqn:H
  | |- POST _ ((if ?cnd then _ else _) _) => destruct cnd eqn:H
  | |- POST _ (abind (abind _ _) _ _) => rewrite abind_assoc; acase H
  end.
Ltac arun lem := eapply POST_bind_run; [apply lem|]; cbv beta iota.
Ltac aleave :=
  first [ rewrite aleave_eq; cbn [POST]
        | rewrite areturn_eq; cbn [POST]
        | eapply POST_bind_leave; [reflexivity|]
        | eapply POST_bind_ret; [reflexivity|] ].
Ltac arun0 := eapply POST_bind_run; [reflexivity|]; cbv beta iota.


Lemma HB_drop : forall h b n, HB h b -> 0 <= n <= b -> HB (Z.shiftr h n) (b - n).
Proof.
  intros h b n [Hb Hh] Hn. unfold HB. split; [lia|].
  rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos n ltac:(lia)).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (n + (b - n)) with b by lia. lia.
Qed.
Lemma HB_0 : HB 0 0.
Proof. unfold HB. cbn. lia. Qed.

Lemma land7_mod : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros b Hb. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section RegsUpd.
  Variable c : icall.
  Lemma REGS_holdbits : forall r h b, REGS c r -> HB h b -> REGS c (irset_bits (irset_hold r h) b).
  Proof.
    intros r h b HR HBn. unfold REGS in *. destruct r; cbn in *.
    destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    repeat (split; [first [assumption | lia]|]). exact A10.
  Qed.
  Lemma REGS_drop : forall r n, REGS c r -> 0 <= n <= ir_bits r ->
    REGS c (irset_bits (irset_hold r (Z.shiftr (ir_hold r) n)) (wrap32 (ir_bits r - n))).
  Proof.
    intros r n HR Hn. pose proof HR as (_ & _ & _ & _ & _ & _ & HBr & _).
    rewrite wrap32_id by (destruct HBr; lia). apply REGS_holdbits; [exact HR|]. apply HB_drop; [exact HBr|exact Hn].
  Qed.
  Lemma REGS_init : forall r, REGS c r -> REGS c (irset_bits (irset_hold r 0) 0).
  Proof. intros r HR. apply REGS_holdbits; [exact HR|exact HB_0]. Qed.
  Lemma REGS_ret : forall r v, REGS c r -> REGS c (irset_ret r v).
  Proof. intros r v HR. unfold REGS in *. destruct r; cbn in *. exact HR. Qed.
  Lemma REGS_out_reg : forall r v, REGS c r -> REGS c (irset_out r v).
  Proof. intros r v HR. unfold REGS in *. destruct r; cbn in *. exact HR. Qed.
  Lemma REGS_copy : forall r ob k,
    REGS c r -> arr_len ob = arr_len (ic_outbuf c) -> 0 <= k -> k <= ir_have r -> k <= ir_left r ->
    REGS (icset_outbuf c ob)
         (irset_put (irset_left (irset_next (irset_have r (wrap32 (ir_have r - k))) (ir_next r + k)) (wrap32 (ir_left r - k))) (ir_put r + k)).
  Proof.
    intros r ob k HR Hob Hk Hkh Hkl. unfold REGS in *. destruct c, r; cbn in *.
    destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    rewrite Hob. rewrite !wrap32_id by lia. repeat (split; [first [assumption | lia]|]). exact A10.
  Qed.
  Lemma REGS_cview : forall c' r, REGS c r -> ic_input c' = ic_input c -> ic_outbuf c' = ic_outbuf c -> REGS c' r.
  Proof. intros c' r HR E1 E2. unfold REGS in *. rewrite E1, E2. exact HR. Qed.
End RegsUpd.

Ltac regs_solve RIN :=
  lazymatch goal with
  | |- REGS _ _ => unfold REGS, HB; sacc; repeat apply conj; first [exact RIN | lia | idtac]
  | |- _ /\ _ => unfold HB; sacc; repeat apply conj; first [exact RIN | lia | idtac]
  end.

Lemma pulled_phi : forall r r', pulled r r' ->
  64 * ir_have r' + 8 * ir_bits r' + 8 * ir_left r' = 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r.
Proof. intros r r' (k & Hk & _ & Hh & _ & Hb & _ & _ & _ & Hl & _). rewrite Hh, Hb, Hl. lia. Qed.
Lemma pulled_out : forall r r', pulled r r' -> ir_out r' = ir_out r /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_ret r' = ir_ret r /\ ir_in r' = ir_in r.
Proof. intros r r' (k & _ & _ & _ & _ & _ & _ & _ & P & L & I & O & T). repeat split; assumption. Qed.

Ltac pstep lem := apply POST_bind; rewrite lem.
Ltac ired := cbv beta iota.
