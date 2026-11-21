(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms Inflate InflateGarbBase InflateGarbFast InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv InflateInvRun InflateInvTab InflateInvKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Ltac ds s :=
  destruct s as [f_mode f_last f_wrap f_havedict f_flags f_dmax f_check f_total f_head f_wbits f_wsize f_whave f_wnext
                 f_window f_window_blk f_hold f_bits f_length f_offset f_extra f_lencode f_distcode f_lenbits f_distbits
                 f_ncode f_nlen f_ndist f_have f_next f_lens f_work f_codes f_sane f_back f_was f_self_blk].

Definition icore (s : inflate_state) :=
  (is_mode s, is_wrap s, is_flags s, is_length s, is_offset s, is_extra s,
   is_lencode s, is_distcode s, is_lenbits s, is_distbits s, is_ncode s, is_nlen s, is_ndist s, is_have s,
   is_next s, is_lens s, is_work s, is_codes s).

Lemma sinv_core : forall s s', icore s' = icore s ->
  0 <= is_whave s' <= is_wsize s' -> 0 <= is_wnext s' <= is_wsize s' -> sinv s -> sinv s'.
Proof.
  intros s s' E W1 W2 SI. ds s. destruct s'. unfold icore in E. cbn in E.
  injection E; intros; subst.
  destruct SI as (_ & _ & REST). cbn in W1, W2.
  split; [exact W1|]. split; [exact W2|]. exact REST.
Qed.

Lemma binv_saved_core : forall s s', icore s' = icore s -> is_hold s' = is_hold s -> is_bits s' = is_bits s ->
  binv_saved s -> binv_saved s'.
Proof.
  intros s s' E Eh Eb B. ds s. destruct s'. unfold icore in E. cbn in E, Eh, Eb.
  injection E; intros; subst. exact B.
Qed.

Lemma cks_core : forall s s', icore s' = icore s -> is_check s' = is_check s -> cks s -> cks s'.
Proof.
  intros s s' E Ec K. ds s. destruct s'. unfold icore in E. cbn in E, Ec.
  injection E; intros; subst. exact K.
Qed.
Lemma cks_restore : forall s h b, cks s -> cks (iset_bits (iset_hold s h) b).
Proof. intros s h b K. ds s. exact K. Qed.

Lemma binv_saved_of_binv : forall s c r,
  binv (mkW s c r) -> is_hold s = ir_hold r -> is_bits s = ir_bits r -> binv_saved s.
Proof. intros s c r B Eh Eb. unfold binv, binv_saved in *. cbn [w_s w_r] in B. rewrite Eh, Eb. exact B. Qed.
Lemma binv_saved_restore : forall s c r,
  binv (mkW s c r) -> binv_saved (iset_bits (iset_hold s (ir_hold r)) (ir_bits r)).
Proof.
  intros s c r B. unfold binv, binv_saved in *. cbn [w_s w_r] in B. destruct s; cbn -[PEND Z.lt] in *. exact B.
Qed.
Lemma sinv_restore : forall s h b, sinv s -> sinv (iset_bits (iset_hold s h) b).
Proof.
  intros s h b SI. pose proof SI as SI0. destruct SI as (W1 & W2 & _).
  apply (sinv_core s); [ds s; reflexivity | ds s; cbn in *; lia | ds s; cbn in *; lia | exact SI0].
Qed.

Lemma binv_of_saved : forall s c r,
  binv_saved s -> ir_hold r = is_hold s -> ir_bits r = is_bits s -> binv (mkW s c r).
Proof. intros s c r B Eh Eb. unfold binv, binv_saved in *. cbn [w_s w_r]. rewrite Eh, Eb. exact B. Qed.


Definition s_entryM (st : inflate_state) : inflate_state :=
  if is_mode st =? TYPE then iset_mode st TYPEDO else st.

Lemma sinv_entry : forall st, sinv st -> sinv (s_entryM st).
Proof.
  intros st SI. unfold s_entryM. destruct (Z.eqb_spec (is_mode st) TYPE); [| exact SI].
  apply sinv_plain; [exact SI|]. pose proof plain_modes as PM. decompose [and] PM; assumption.
Qed.

Lemma binv_saved_entry : forall st, binv_saved st -> binv_saved (s_entryM st).
Proof.
  intros st B. unfold s_entryM. destruct (Z.eqb_spec (is_mode st) TYPE) as [E|]; [| exact B].
  unfold binv_saved in *. rewrite E in B. destruct st; cbn -[PEND Z.lt] in *.
  destruct B as [B|B]; [left; exact B | right]. revert B. pend_red. intros B. exact B.
Qed.

Lemma cks_entry : forall st, cks st -> cks (s_entryM st).
Proof.
  intros st CK. unfold s_entryM. destruct (Z.eqb_spec (is_mode st) TYPE) as [E|]; [| exact CK].
  unfold cks in *. rewrite E in CK. destruct st; cbn -[Z.le Z.land ck_adl] in *. intros _ Hw Hf. apply CK; [| exact Hw | exact Hf].
  unfold TYPE, CHECK. lia.
Qed.

Section Entry.
  Variables (NI NO WN TOT0 : Z).
  Hypothesis NI32 : 0 <= NI < 2 ^ 32.
  Hypothesis NO32 : 0 <= NO < 2 ^ 32.

  Definition W1M (st : inflate_state) (c : icall) : iw :=
    mkW (s_entryM st) c
        (mkIR (ic_next_in c) (ic_avail_in c) (ic_next_out c) (ic_avail_out c)
              (is_hold (s_entryM st)) (is_bits (s_entryM st)) (ic_avail_in c) (ic_avail_out c) Z_OK).

  Theorem pinv_entry : forall st c,
    LRNGq NI NO WN TOT0 (W1M st c) -> sinv st -> binv_saved st -> cks st -> ic_next_out c = 0 ->
    pinv NI NO WN TOT0 (W1M st c).
  Proof.
    intros st c LR SI BS CK Hno. unfold pinv. split; [split; assumption|]. split; [exact LR|].
    split; [cbn [W1M w_s]; apply sinv_entry; exact SI|]. split; [| split].
    - unfold xinv, W1M. cbn [w_s w_c w_r ir_ret ir_put ir_out ir_left ic_next_out]. split; [left; reflexivity|]. split; [lia|]. left. lia.
    - unfold W1M. apply binv_of_saved; [apply binv_saved_entry; exact BS | reflexivity | reflexivity].
    - unfold cinv, W1M. cbn [w_s w_c w_r ir_put ir_out ir_left ir_have ir_hold ir_bits ic_next_out ic_avail_in ic_avail_out].
      split; [apply cks_entry; exact CK|]. split; [intros _; reflexivity|]. split; [intros _; repeat split; try reflexivity; symmetry; exact Hno|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; lia.
  Qed.
End Entry.


Lemma resetkeep_ok : forall iv s z s' z' rc,
  inflateResetKeep iv s z = (s', z', rc) -> rc = Z_OK ->
  0 <= is_whave s <= is_wsize s -> 0 <= is_wnext s <= is_wsize s ->
  arr_len (is_lens s) = 320 -> arr_len (is_work s) = 288 -> arr_len (is_codes s) = 1444 ->
  sinv s' /\ binv_saved s' /\ cks s'.
Proof.
  intros iv s z s' z' rc E Hrc W1 W2 A1 A2 A3. unfold inflateResetKeep in E.
  destruct (inflateStateCheck s); [injection E; intros; subst; discriminate|].
  unfold auxp in E. ds s.
  destruct (iv_aux iv); wred in E; injection E; intros <- <- <-;
    cbn [is_whave is_wsize is_wnext is_lens is_work is_codes] in *;
    (split; [unfold sinv; cbn -[Z.shiftl tables_ok ctab_ok tables_rep ctab_rep arr_get arr_len codes_live Z.pow];
             repeat match goal with |- _ /\ _ => split end; try assumption; try lia; intros HX;
             first [discriminate HX | destruct HX as [HX|HX]; discriminate HX]
           | split; [unfold binv_saved; cbn [is_bits]; left; lia
                    | unfold cks; cbn [is_mode]; intros HX; exfalso; unfold HEAD, TYPE, CHECK in HX; lia]]).
Qed.

Lemma reset_ok : forall iv s z s' z' rc,
  inflateReset iv s z = (s', z', rc) -> rc = Z_OK ->
  arr_len (is_lens s) = 320 -> arr_len (is_work s) = 288 -> arr_len (is_codes s) = 1444 ->
  sinv s' /\ binv_saved s' /\ cks s'.
Proof.
  intros iv s z s' z' rc E Hrc A1 A2 A3. unfold inflateReset in E.
  destruct (inflateStateCheck s) eqn:CK; [injection E; intros; subst; discriminate|].
  apply (resetkeep_ok iv _ z s' z' rc E Hrc); ds s; cbn; try lia; assumption.
Qed.

Lemma is_of_oracle_lens : forall lay g b,
  arr_len (is_lens (is_of_oracle lay g b)) = 320 /\ arr_len (is_work (is_of_oracle lay g b)) = 288
  /\ arr_len (is_codes (is_of_oracle lay g b)) = 1444.
Proof. intros. cbn. repeat split; reflexivity. Qed.
