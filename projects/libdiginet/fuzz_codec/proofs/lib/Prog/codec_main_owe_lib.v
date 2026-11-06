(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 268 of its 289 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_cells codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

(** ---- words ---- *)

Lemma sx32_lit : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma mod64_zero : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 = 0 -> x = 0.
Proof. intros x Hx H. Z.div_mod_to_equations. lia. Qed.

Lemma neg_lit : forall z, 0 < z < 2 ^ 63 -> Z_to_bv 64 (2 ^ 64 - z) = Z_to_bv 64 (- z).
Proof. intros z Hz. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). Z.div_mod_to_equations. lia. Qed.

(** A 32-bit field loaded with lw: the sign-extended word. *)
Lemma sx32_u32 : forall x, 0 <= x < 2 ^ 32 ->
  (x < 2 ^ 31 /\ bv_unsigned (sx32 (Z_to_bv 64 x)) = x) \/
  (2 ^ 31 <= x /\ bv_unsigned (sx32 (Z_to_bv 64 x)) = x + (2 ^ 64 - 2 ^ 32)).
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  destruct (Z.ltb_spec x (2 ^ 31)); [left | right]; (split; [lia|]); Z.div_mod_to_equations; lia.
Qed.

(** A byte store (sb) writes le1 v: the cell C1 of v's low byte. *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Lemma byte_eq : forall x y, x mod 2 ^ 8 = y mod 2 ^ 8 -> Z_to_bv 8 x = b8 y.
Proof. intros x y H. unfold b8. apply Z_to_bv8_mod. exact H. Qed.

(** A stored byte equals the owed one. *)
Ltac byte_tac :=
  apply byte_eq; unfold u8;
  rewrite ?unsigned_lit_wrap, ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  Z.div_mod_to_equations; lia.

(** ---- the desk bytes owe() reads at k.desk + 8 .. 11 ---- *)

Lemma desk_cases : forall pv dv d, pd_ok pv dv (Some d) -> (d = c24 /\ dv = 0x1f208) \/ (d = pc /\ dv = 0x1f218).
Proof.
  intros pv dv d [(_ & _ & H) | [(_ & -> & H) | (_ & -> & H)]]; [discriminate | left | right];
    injection H as ->; split; reflexivity.
Qed.

Lemma desk_rng : forall pv dv d, pd_ok pv dv (Some d) ->
  0 <= d_dev d <= 1 /\ 8 <= d_strips d <= 24 /\ 4 <= d_chars d <= 8 /\ 9 <= d_counter d <= 25.
Proof. intros pv dv d H. destruct (desk_cases pv dv d H) as [[-> _] | [-> _]]; cbn; lia. Qed.

Lemma desk_rd : forall e m1 pv dv d j, env_ok e -> fr_ok e m1 -> pd_ok pv dv (Some d) -> 0 <= j < 4 ->
  ov_read_bytes rsegs m1 (wa (dv + 8 + j)) 1 =
    Some [nth (Z.to_nat j) (bz [d_dev d; d_strips d; d_chars d; d_counter d]) (Z_to_bv 8 0)].
Proof.
  intros e m1 pv dv d j HE HF Hpd Hj.
  apply bytes_at_byte; [ exact (desk_bytes_of_pd m1 pv dv d (relro_of_fr e m1 HE HF) Hpd) | cbn; lia ].
Qed.

Lemma desk_dev_rd : forall e m1 pv dv d, env_ok e -> fr_ok e m1 -> pd_ok pv dv (Some d) ->
  ov_read_bytes rsegs m1 (wa (dv + 8)) 1 = Some [b8 (d_dev d)].
Proof.
  intros e m1 pv dv d HE HF Hpd. replace (dv + 8) with (dv + 8 + 0) by lia.
  exact (desk_rd e m1 pv dv d 0 HE HF Hpd ltac:(lia)).
Qed.

Lemma desk_strips_rd : forall e m1 pv dv d, env_ok e -> fr_ok e m1 -> pd_ok pv dv (Some d) ->
  ov_read_bytes rsegs m1 (wa (dv + 9)) 1 = Some [b8 (d_strips d)].
Proof.
  intros e m1 pv dv d HE HF Hpd. replace (dv + 9) with (dv + 8 + 1) by lia.
  exact (desk_rd e m1 pv dv d 1 HE HF Hpd ltac:(lia)).
Qed.

Lemma desk_counter_rd : forall e m1 pv dv d, env_ok e -> fr_ok e m1 -> pd_ok pv dv (Some d) ->
  ov_read_bytes rsegs m1 (wa (dv + 11)) 1 = Some [b8 (d_counter d)].
Proof.
  intros e m1 pv dv d HE HF Hpd. replace (dv + 11) with (dv + 8 + 3) by lia.
  exact (desk_rd e m1 pv dv d 3 HE HF Hpd ltac:(lia)).
Qed.

(** ---- owe()'s answer in the want fields ---- *)

Lemma owe_want_range : forall k od, fst (owe_k k od) = E_RANGE ->
  k_want_rc k = -11 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 -> owe_want_ok k od.
Proof.
  intros k od H H1 H2 H3 H4. unfold owe_want_ok. rewrite H. unfold E_RANGE.
  split; [exact H1|]. cbn [Z.eqb]. tauto.
Qed.

Lemma owe_want_succ : forall k od bs key dp, owe_k k od = (0, (bs, key, dp)) ->
  k_want_rc k = 0 -> k_want_len k = Z.of_nat (length bs) -> firstn (length bs) (k_want k) = bz bs ->
  k_want_key k = key -> k_want_display k = dp -> owe_want_ok k od.
Proof.
  intros k od bs key dp H H1 H2 H3 H4 H5. unfold owe_want_ok. rewrite H. cbn [fst snd Z.eqb].
  split; [exact H1|]. tauto.
Qed.

(** ---- the personality ---- *)

Lemma od_ok_of_pd : forall pv dv od, pd_ok pv dv od -> od_ok od.
Proof. intros pv dv od [(_ & _ & ->) | [(_ & _ & ->) | (_ & _ & ->)]]; unfold od_ok; tauto. Qed.

Lemma pd_range : forall pv dv od, pd_ok pv dv od -> 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64.
Proof.
  intros pv dv od [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold PERS; lia.
Qed.

(** ---- the codes owe() and the encoders return ---- *)

Definition code_ok (r : Z) : Prop := r = 0 \/ r = -1 \/ r = -5 \/ r = -10 \/ r = -11.

Lemma owe_codes : forall kind od a b c delta bytes n, code_ok (fst (owe_spec kind od a b c delta bytes n)).
Proof.
  intros. unfold owe_spec, code_ok, E_ARG, E_RANGE, E_SPACE, E_REFUSED.
  destruct od as [d|]; cbv beta iota zeta;
    repeat (match goal with
            | |- context [if ?c then _ else _] => destruct c
            | |- context [match ?x with pair _ _ => _ end] => destruct x
            end; cbv beta iota);
    cbn [fst]; lia.
Qed.

(** The encoder's code is owe()'s, and on success its command is owe()'s (codec_agree.agree_all). *)
Lemma enc_agree : forall k od, rec_ok k od ->
  fst (enc_k k od) = fst (owe_k k od) /\
  (fst (enc_k k od) = 0 -> snd (enc_k k od) = Some (snd (owe_k k od))).
Proof.
  intros k od (Hk & Hpd & Hr & _ & _).
  pose proof (agree_all (k_kind k) od (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                Hk (od_ok_of_pd _ _ _ Hpd) Hr) as A.
  unfold agrees in A. unfold enc_k, owe_k.
  destruct (enc_of_call _ _ _ _ _ _ _ _) as [rc o]. cbn [fst snd] in *.
  destruct A as [A1 A2]. split; [symmetry; exact A1 | exact A2].
Qed.

Lemma owe_k_code : forall k od, code_ok (fst (owe_k k od)).
Proof. intros k od. apply owe_codes. Qed.

(** The command owe() owes on success is well formed (codec_agree.owe_ok_wf). *)
Lemma owe_k_wf : forall k od, rec_ok k od -> fst (owe_k k od) = 0 -> cmd_wf (snd (owe_k k od)).
Proof.
  intros k od (Hk & Hpd & Hr & _ & _) H0.
  exact (owe_ok_wf (k_kind k) od (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
           Hk (od_ok_of_pd _ _ _ Hpd) Hr H0).
Qed.

(** ---- the ranges the checks take (kcall_wf) ---- *)

Lemma kwf_of : forall k od, rec_ok k od -> k_rc k = fst (enc_k k od) -> owe_want_ok k od -> kcall_wf k.
Proof.
  intros k od HR Hrc [Hwrc Hw].
  pose proof HR as (Hk & Hpd & Hr & _ & _).
  destruct (enc_agree k od HR) as [EA _].
  pose proof (owe_k_code k od) as C. unfold code_ok in C.
  pose proof (pd_range _ _ _ Hpd) as [Hp Hd].
  unfold rdr_k, reader_ok in Hr. destruct Hr as (Ha & Hb & Hc & Hdl & _ & _ & Hn & _).
  unfold kcall_wf.
  destruct (Z.eqb_spec (fst (owe_k k od)) 0) as [E0 | E0].
  - pose proof (owe_k_wf k od HR E0) as W.
    try rewrite E0 in Hw. cbn [Z.eqb] in Hw.
    destruct (snd (owe_k k od)) as [[bs key] dp]. unfold cmd_wf in W. cbv beta iota in W, Hw.
    destruct Hw as (Hl & _ & Hkey & Hdp). destruct W as (W1 & _ & W3 & W4).
    repeat split; lia.
  - assert (E0' : (fst (owe_k k od) =? 0) = false) by (apply Z.eqb_neq; exact E0).
    try rewrite E0' in Hw. cbn [Z.eqb] in Hw. destruct Hw as (Hl & Hkey & Hdp).
    repeat split; lia.
Qed.

(** ---- the command an encoder writes over 0xa5^32 ---- *)

Lemma fa5_firstn_skipn : forall n, (n <= 24)%nat ->
  skipn n (firstn 24 (fa5 32)) = repeat (b8 0xa5) (24 - n).
Proof.
  intros n Hn. unfold fa5.
  do 25 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma fold_key_le_val : forall l : list byte,
  fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 l = le_val (map bv_unsigned l).
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma cmd_key_le4 : forall key, 0 <= key < 2 ^ 32 ->
  fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 (le4 (Z_to_bv 64 key)) = key.
Proof.
  intros key Hk. rewrite fold_key_le_val, <- bytes_le_to_Z_le_val, bytes_le_to_Z_le4.
  rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma b8_small : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma cmd_out_fields : forall bs key dp, cmd_wf (bs, key, dp) ->
  cmd_len (cmd_out (fa5 32) (Some (bs, key, dp))) = Z.of_nat (length bs) /\
  firstn (length bs) (cmd_out (fa5 32) (Some (bs, key, dp))) = bz bs /\
  cmd_key (cmd_out (fa5 32) (Some (bs, key, dp))) = key /\
  cmd_display (cmd_out (fa5 32) (Some (bs, key, dp))) = dp.
Proof.
  intros bs key dp (Hl & _ & Hk & Hd). unfold cmd_out.
  rewrite fa5_firstn_skipn by exact Hl.
  change (firstn 2 (skipn 26 (fa5 32))) with [b8 0xa5; b8 0xa5].
  rewrite (app_assoc (bz bs) (repeat (b8 0xa5) (24 - length bs))).
  assert (L24 : length (bz bs ++ repeat (b8 0xa5) (24 - length bs)) = 24%nat)
    by (unfold bz; rewrite length_app, length_map, repeat_length; lia).
  unfold cmd_len, cmd_key, cmd_display.
  split; [| split; [| split]].
  - rewrite app_nth2 by lia. rewrite L24, Nat.sub_diag. cbn [bz map nth app].
    apply b8_small. lia.
  - rewrite <- (app_assoc (bz bs)). unfold bz. rewrite <- (length_map b8 bs).
    apply firstn_app_exact.
  - rewrite skipn_app, L24.
    replace (skipn 28 (bz bs ++ repeat (b8 0xa5) (24 - length bs))) with (@nil byte)
      by (symmetry; apply skipn_all2; lia).
    replace (28 - 24)%nat with 4%nat by reflexivity. cbn [app bz map skipn].
    change (skipn 0 (le4 (Z_to_bv 64 key))) with (le4 (Z_to_bv 64 key)).
    assert (L4 : length (le4 (Z_to_bv 64 key)) = 4%nat) by apply length_le4.
    rewrite firstn_all2 by lia. apply cmd_key_le4. exact Hk.
  - rewrite app_nth2 by lia. rewrite L24. replace (25 - 24)%nat with 1%nat by reflexivity. cbn [bz map nth app].
    apply b8_small. lia.
Qed.

(** ---- the call record in the frame ---- *)

Lemma body_k_at : forall e m k c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  cells_at rsegs m (bv_unsigned (e_sp e) + -384) (kcall_cells k).
Proof.
  intros e m k c rem tl H. unfold body_cells in H.
  apply rw_cells_app_split in H. destruct H as [_ H].
  apply rw_cells_app_split in H. destruct H as [H _].
  cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 16) with (bv_unsigned (e_sp e) + -384) in H by lia.
  exact (proj1 H).
Qed.

(** The frame with the record's fields as cells and owe()'s want fields: the 24 want bytes as any cells w,
    want_len, want_key and want_display. *)
Lemma body_of_flat : forall e m k c rem tl rc wrc w wl wk wd,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
      CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 rc);
      CB 32 (k_before k); CB 32 (k_out k); C4 (Z_to_bv 64 wrc)] ++ w ++
     [C8 (Z_to_bv 64 wl); C4 (Z_to_bv 64 wk); C4 (Z_to_bv 64 wd);
      C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl]) ->
  cells_size w = 24%nat ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    (body_cells e (mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
                           (k_bytes k) (k_n k) rc (k_before k) (k_out k) wrc (cells_bytes w) wl wk wd) c rem tl).
Proof.
  intros e m k c rem tl rc wrc w wl wk wd H Hs.
  pose proof (rw_cells_merge rsegs m _ _ w _ H) as M. rewrite Hs in M. exact M.
Qed.

(** As body_of_flat, with want_key and want_display zeroed by one 8-byte store. *)
Lemma le8_zero_split : le8 (Z_to_bv 64 0) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).
Proof. vm_compute. reflexivity. Qed.

Lemma body_of_flat0 : forall e m k c rem tl rc wrc w wl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
      CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 rc);
      CB 32 (k_before k); CB 32 (k_out k); C4 (Z_to_bv 64 wrc)] ++ w ++
     [C8 (Z_to_bv 64 wl); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl]) ->
  cells_size w = 24%nat ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    (body_cells e (mkKcall (k_kind k) (k_pad k) (k_p k) (k_desk k) (k_a k) (k_b k) (k_c k) (k_delta k)
                           (k_bytes k) (k_n k) rc (k_before k) (k_out k) wrc (cells_bytes w) wl 0 0) c rem tl).
Proof.
  intros e m k c rem tl rc wrc w wl H Hs.
  apply (body_of_flat e m k c rem tl rc wrc w wl 0 0); [| exact Hs].
  destruct H as [[Hwf Hb] Hw]. split; [split|].
  - apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [W2 W3].
    apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [exact W2|].
    cbn in W3 |- *. tauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes app] in *.
    rewrite le8_zero_split, <- app_assoc in Hb. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize Nat.add] in *. exact Hw.
Qed.

(** The frame of a record whose want_key and want_display one 8-byte store will zero. *)
Lemma flat_of_body : forall e m k c rem tl,
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400)
    ([C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
      C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
      C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
      CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k));
      CB 32 (k_before k); CB 32 (k_out k); C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k);
      C8 (Z_to_bv 64 (k_want_len k));
      CB 8 (cells_bytes [C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))]);
      C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl]).
Proof.
  intros e m k c rem tl H. unfold body_cells in H. cbn [kcall_cells app] in H.
  exact (rw_cells_merge rsegs m _
           [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0);
            C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
            C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
            CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k));
            CB 32 (k_before k); CB 32 (k_out k); C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k);
            C8 (Z_to_bv 64 (k_want_len k))]
           [C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))]
           [C8 (Z_to_bv 64 (bv_unsigned (e_p e) + c)); C8 (Z_to_bv 64 rem); CB 80 tl] H).
Qed.

(** Pick the want cells out of a flat frame (the 16 cells before them, the 6 after) and rebuild the body. *)
Ltac drop16 l :=
  lazymatch l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?r => r end.
Ltac but_last6 l :=
  lazymatch l with
  | [_; _; _; _; _; _] => constr:(@nil cell)
  | ?x :: ?r => let r' := but_last6 r in constr:(x :: r')
  end.
Ltac but_last5 l :=
  lazymatch l with
  | [_; _; _; _; _] => constr:(@nil cell)
  | ?x :: ?r => let r' := but_last5 r in constr:(x :: r')
  end.
Ltac to_body FL :=
  lazymatch type of FL with
  | rw_cells _ _ _ ?cs =>
    let r := drop16 cs in
    let w6 := but_last6 r in
    let w5 := but_last5 r in
    first [ apply (body_of_flat _ _ _ _ _ _ _ _ w6) in FL; [| reflexivity]
          | apply (body_of_flat0 _ _ _ _ _ _ _ _ w5) in FL; [| reflexivity] ]
  end.
