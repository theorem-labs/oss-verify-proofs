(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 1475 of its 1496 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import memset_c memcpy_c dt1_head_c name_field_c
  build_dt1_single_c reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* A branch whose condition the hypotheses decide false; literals and in-range Z_to_bv words are unfolded. *)
Ltac cond_unlit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
  end.
Ltac nf := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac nt := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac bstep := step; nf.

Lemma mb_word : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma mb_stk_hi : forall segs m lo h hi, stk segs m lo h -> h = hi -> stk segs m lo hi.
Proof. intros; subst; assumption. Qed.

Ltac mb_early_epi :=
  do 8 step;
  apply evt_done; unfold reac_box_model_block_post;
  lazymatch goal with H0 : _ \/ _ |- context [(?x =? 0) || (?y =? 0)] =>
    replace ((x =? 0) || (y =? 0)) with true
      by (symmetry; apply orb_true_iff; destruct H0; [left | right]; apply Z.eqb_eq; lia) end;
  do 15 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with ST : stk _ _ _ _, FR : rw_cells _ _ _ _ |- _ =>
    pose proof (stk_release rsegs _ _ _ _ ST FR ltac:(lia)) as STf; cbn [cells_size csize Nat.add] in STf;
    apply (mb_stk_hi _ _ _ _ _ STf); lia end.

(* p = 0 or o = 0: the prologue, the early return, the epilogue. *)
Lemma mb_early : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (row nb : list byte),
  stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp) -> mem_inv rsegs m ->
  (bv_unsigned a0 = 0 \/ bv_unsigned a2 = 0) ->
  evt rsegs
    (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
       (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) row nb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m row nb
    ST MI H0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Rlo & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold REAC_BOX_MODEL_BLOCK.
  step.
  carve_frame 80%nat ST.
  step. step. step. step. step. step. step.
  destruct (Z.eq_dec (bv_unsigned a0) 0) as [Z0|Z0].
  - nt. mb_early_epi.
  - nf. step. step. nt. mb_early_epi.
Qed.

Ltac dj := cbn [disjoint_from outside cells_size csize Nat.add]; repeat split; try exact I; lia.
Ltac sfp := unfold sub_fp; cbn [outside]; intros; repeat split; try exact I; lia.

Lemma mb_rw1 : forall segs m A n X, rw_cells segs m A [CB n X] -> bytes_at segs m A X.
Proof. intros segs m A n X [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. Qed.

(* A callee wrote Y at [A+k, A+k+n) of the cell [CB N X] and nothing else of it. *)
Lemma mb_upd : forall segs m m' A N X k n Y W,
  rw_cells segs m A [CB N X] -> (k + n <= N)%nat -> munch W m m' -> wmono segs m m' ->
  disjoint_from W A (Z.of_nat k) -> disjoint_from W (A + Z.of_nat (k + n)) (Z.of_nat (N - (k + n))) ->
  bytes_at segs m' (A + Z.of_nat k) Y -> length Y = n ->
  rw_cells segs m' A [CB N (upd_bytes X k Y)].
Proof.
  intros segs m m' A N X k n Y W [[Hwf HB] HW] Hkn MU WM D1 D2 HBY LY.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [LX _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
  pose proof (bytes_at_sub segs m A X 0 k HB ltac:(lia)) as B1.
  change (skipn 0 X) with X in B1. cbn [Z.of_nat] in B1. rewrite Z.add_0_r in B1.
  pose proof (bytes_at_sub segs m A X (k + n) (N - (k + n)) HB ltac:(lia)) as B3.
  rewrite firstn_all2 in B3 by (rewrite length_skipn; lia).
  apply (bytes_at_transport segs W m m') in B1;
    [|exact MU | rewrite length_firstn; replace (Nat.min k (length X)) with k by lia; exact D1].
  apply (bytes_at_transport segs W m m') in B3;
    [|exact MU | rewrite length_skipn; replace (length X - (k + n))%nat with (N - (k + n))%nat by lia; exact D2].
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by lia; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold upd_bytes. apply bytes_at_app. split; [exact B1|].
    rewrite length_firstn. replace (Nat.min k (length X)) with k by lia.
    apply bytes_at_app. split; [exact HBY|]. rewrite LY.
    replace (A + Z.of_nat k + Z.of_nat n) with (A + Z.of_nat (k + n)) by lia. exact B3.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_transport; [exact HW | exact WM].
Qed.

(* The bytes of the cells [mid] of a cell list. *)
Lemma mb_mid : forall segs m A pre mid post, rw_cells segs m A (pre ++ mid ++ post) ->
  bytes_at segs m (A + Z.of_nat (cells_size pre)) (cells_bytes mid).
Proof.
  intros segs m A pre mid post [[Hwf HB] _].
  apply cells_wf_app in Hwf. destruct Hwf as [Hpre _].
  rewrite !cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  apply bytes_at_app in HB. destruct HB as [HB _].
  rewrite cells_bytes_length in HB by exact Hpre. exact HB.
Qed.

Lemma mb_l4 : forall a b c d e f g h : byte, a = e -> b = f -> c = g -> d = h -> [a; b; c; d] = [e; f; g; h].
Proof. intros; subst; reflexivity. Qed.

Lemma mb_synth3 : forall row nb, synth row 3 nb = if fwm row <=? 9999 then dt1s 0 (digits (fwm row)) else zeros 32.
Proof. reflexivity. Qed.
Lemma mb_rc3 : forall row, rc row 3 = if fwm row <=? 9999 then 1 else -1.
Proof. reflexivity. Qed.

Lemma mb_synth4 : forall row nb, synth row 4 nb = dt1s 1536 (rvb row).
Proof. reflexivity. Qed.
Lemma mb_rc4 : forall row, rc row 4 = 1.
Proof. reflexivity. Qed.

Lemma mb_cons : forall (a b : byte) l l', a = b -> l = l' -> a :: l = b :: l'.
Proof. intros; subst; reflexivity. Qed.

Lemma mb_whi : forall w, 0 <= w < 65536 -> whi w = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 w) ≫ 8))).
Proof.
  intros w Hw. unfold whi, bz. apply Z_to_bv8_mod. rewrite (unsigned_lit w) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite (unsigned_lit (w / 256)) by lia.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mb_wlo : forall w, 0 <= w < 65536 -> wlo w = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 w)).
Proof.
  intros w Hw. unfold wlo, bz. apply Z_to_bv8_mod. rewrite unsigned_lit by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma mb_synth5 : forall row nb, synth row 5 nb = if has row =? 0 then zeros 32 else idf (nmr row nb).
Proof. reflexivity. Qed.
Lemma mb_rc5 : forall row, rc row 5 = if has row =? 0 then 0 else 1.
Proof. reflexivity. Qed.
Lemma mb_synth6 : forall row nb, synth row 6 nb = if has row =? 0 then zeros 32 else idl (nmr row nb).
Proof. reflexivity. Qed.
Lemma mb_rc6 : forall row, rc row 6 = if has row =? 0 then 0 else 1.
Proof. reflexivity. Qed.

(* One CB cell and the cells after it, as one CB cell, and back. *)
Lemma mb_flat : forall segs m A N X cs, rw_cells segs m A (CB N X :: cs) ->
  rw_cells segs m A [CB (N + cells_size cs) (X ++ cells_bytes cs)].
Proof.
  intros segs m A N X cs [[[LX Hcs] HB] HW]. cbn [cell_wf] in LX.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_app, cells_bytes_length by exact Hcs. lia.
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize] in *. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma mb_unflat : forall segs m A N X cs, rw_cells segs m A [CB (N + cells_size cs) (X ++ cells_bytes cs)] ->
  length X = N -> cells_wf cs -> rw_cells segs m A (CB N X :: cs).
Proof.
  intros segs m A N X cs [[_ HB] HW] LX Hcs.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LX | exact Hcs].
  - cbn [cells_bytes cbytes] in *. rewrite app_nil_r in HB. exact HB.
  - cbn [cells_size csize] in *. rewrite Nat.add_0_r in HW. exact HW.
Qed.

Lemma mb_upd_app : forall (X R Y : list byte) k, (k + length Y <= length X)%nat ->
  upd_bytes (X ++ R) k Y = upd_bytes X k Y ++ R.
Proof.
  intros X R Y k H. unfold upd_bytes. rewrite firstn_app, skipn_app.
  replace (k - length X)%nat with 0%nat by lia. replace (k + length Y - length X)%nat with 0%nat by lia.
  cbn [firstn skipn]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma mb_first_upd : forall (X Y : list byte) k, length X = 32%nat -> (k + length Y = 31)%nat ->
  firstn 31 (upd_bytes X k Y) = firstn k X ++ Y.
Proof.
  intros X Y k LX LY. unfold upd_bytes. rewrite LY, app_assoc, firstn_app, length_app, length_firstn.
  replace (31 - (Nat.min k (length X) + length Y))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply firstn_all2. rewrite length_app, length_firstn. lia.
Qed.

Lemma mb_nmf_len : forall nb, (length nb <= 16)%nat -> length (nmf nb) = 16%nat.
Proof. intros nb L. unfold nmf. rewrite length_app, repeat_length. pose proof (rs_takenz_len nb). lia. Qed.

Lemma mb_sx32_eq0 : forall x, 0 <= x < 2^32 -> bv_eqb (sx32 (Z_to_bv 64 x)) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold sx32, bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. split; intros H; lia.
Qed.

(* A list of closed bytes, byte by byte. *)
Ltac mb_bytes :=
  repeat (apply mb_cons; [first [reflexivity | apply Z_to_bv8_mod; vm_compute; reflexivity] |]); reflexivity.

Lemma mb_stamp8 : forall s,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 s)))))
                                     127))) = Z_to_bv 8 ((- s) mod 128).
Proof. intros s. exact (f_equal (hd (bz 0)) (rc_le1_stamp s)). Qed.

Lemma mb_psum_app : forall A B k, psum (A ++ B) (length A + k) = psum A (length A) + psum B k.
Proof.
  intros A B k. induction k as [|k IH].
  - rewrite Nat.add_0_r, psum_app_l by lia. cbn [psum]. lia.
  - rewrite Nat.add_succ_r. cbn [psum]. rewrite IH, app_nth2 by lia.
    replace (length A + k - length A)%nat with k by lia. lia.
Qed.

Lemma mb_sltiu1 : forall x, 0 <= x < 2^64 - 10 -> v_sltiu (Z_to_bv 64 x) (-10) = Z_to_bv 64 1.
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by lia.
  assert (E : bv_wrap 64 (-10) = 18446744073709551606) by reflexivity. rewrite E.
  replace (x <? 18446744073709551606) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mb_idl_eq : forall (H S6 : list byte) c, length H = 9%nat -> length S6 = 6%nat ->
  firstn 31 (upd_bytes (upd_bytes (H ++ zeros 23) 9 S6) 15 [c; bz 247]) = H ++ S6 ++ [c; bz 247] ++ zeros 14.
Proof.
  intros H S6 c LH LS.
  change (H ++ zeros 23) with (H ++ [] ++ zeros 23).
  rewrite (rs_upd_fill H [] S6 23 9) by (cbn [length]; lia). rewrite LS.
  change (H ++ ([] ++ S6) ++ zeros (23 - 6)) with (H ++ S6 ++ zeros 17).
  rewrite (rs_upd_fill H S6 [c; bz 247] 17 15) by (cbn [length]; lia).
  change (17 - length [c; bz 247])%nat with 15%nat.
  assert (E : H ++ (S6 ++ [c; bz 247]) ++ zeros 15 = (H ++ S6 ++ [c; bz 247] ++ zeros 14) ++ [bz 0])
    by (rewrite <- !app_assoc; reflexivity).
  rewrite E.
  assert (L : length (H ++ S6 ++ [c; bz 247] ++ zeros 14) = 31%nat) by (rewrite !length_app, LH, LS; reflexivity).
  rewrite <- L at 1. apply firstn_app_exact.
Qed.

(* A branch whose condition is closed and false. *)
Ltac nfc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.

(* A byte store at offset 0 of a pointer register: give the store the form of a cell store. *)
Ltac st0 := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?x ?bs) _) =>
      is_var x;
      replace (write_to_mem mm x bs) with (write_to_mem mm (wa (bv_unsigned x + Z.of_nat 0)) bs)
        by (f_equal; symmetry; apply rc_wa_add0)
  end; mem_after_store_opt.

Lemma mb_synth0 : forall row nb, synth row 0 nb = if synok row then gram row else zeros 32.
Proof. reflexivity. Qed.
Lemma mb_rc0 : forall row, rc row 0 = if synok row then 1 else -1.
Proof. reflexivity. Qed.

Lemma mb_synok_iff : forall row, synok row = true <->
  0 <= ic row /\ 0 <= oc row /\ ic row mod 4 = 0 /\ oc row mod 4 = 0 /\ ic row / 4 + oc row / 4 <= 12.
Proof. intros r. unfold synok. rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq. tauto. Qed.

Lemma mb_synok_false : forall row,
  ~ (0 <= ic row /\ 0 <= oc row /\ ic row mod 4 = 0 /\ oc row mod 4 = 0 /\ ic row / 4 + oc row / 4 <= 12) ->
  synok row = false.
Proof. intros r H. destruct (synok r) eqn:E; [|reflexivity]. exfalso. apply H. apply mb_synok_iff. exact E. Qed.

Lemma mb_sltu0 : forall x (y : word), bv_unsigned y <= x < 2^64 -> v_sltu (Z_to_bv 64 x) y = Z_to_bv 64 0.
Proof.
  intros x y H. pose proof (zr_word y) as Ry. unfold inr64 in Ry.
  unfold v_sltu, c_ltu, bv_ltu. rewrite unsigned_lit by lia.
  replace (x <? bv_unsigned y) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mb_slti0 : forall x, 0 <= x < 2^63 -> v_slti (Z_to_bv 64 x) 0 = Z_to_bv 64 0.
Proof.
  intros x H. unfold v_slti, zsig. rewrite zb_signed, unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (x <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma mb_lts_lit : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed. rewrite !unsigned_lit by lia.
  replace (x <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (y <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mb_addiw : forall x d, 0 <= x < 2^64 -> 0 <= x + d < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + d)) = Z_to_bv 64 (x + d).
Proof. intros x d H1 H2. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

Lemma mb_swrap_lit : forall x, 0 <= x < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x))) = Z_to_bv 64 x.
Proof. intros x H. rewrite unsigned_lit by lia. rewrite rc_swrap_small by lia. reflexivity. Qed.

Lemma mb_zext32 : forall x, 0 <= x < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 32))) 32 = x.
Proof.
  intros x H. rewrite (unsigned_lit x) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

Lemma mb_rep_snoc : forall (x : byte) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros x n. induction n as [|n IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity. Qed.

Lemma mb_fill_step : forall (H P : list byte) b, length H = 8%nat -> (length P < 24)%nat ->
  upd_bytes (H ++ P ++ zeros (24 - length P)) (8 + length P) [b] = H ++ (P ++ [b]) ++ zeros (24 - length (P ++ [b])).
Proof.
  intros H P b LH LP. rewrite (rs_upd_fill H P [b] (24 - length P) (8 + length P)) by (cbn [length]; lia).
  rewrite length_app. cbn [length].
  replace (24 - length P - 1)%nat with (24 - (length P + 1))%nat by lia. reflexivity.
Qed.

Ltac bst := step; first [nf | nfc].

Section Main.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wp wb wo : word) (row nb ob : list byte).
  Hypothesis HMS : memset_contract.
  Hypothesis HMC : memcpy_contract.
  Hypothesis HDH : dt1_head_contract.
  Hypothesis HNF : name_field_contract.
  Hypothesis HBD : build_dt1_single_contract.
  Hypothesis Rsp : 0 <= bv_unsigned sp < 2^64.
  Hypothesis Rlo : 0 <= bv_unsigned sp - 112.
  Hypothesis Hp : 0 < bv_unsigned wp.
  Hypothesis Ho : 0 < bv_unsigned wo.
  Hypothesis Ho32 : bv_unsigned wo + 32 <= 2^64.
  Hypothesis Hp296 : bv_unsigned wp + 296 <= 2^64.
  Hypothesis DOS : bv_unsigned sp <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned sp - 112.
  Hypothesis DOJ : bv_unsigned wo + 32 <= JOIN_0013 \/ JOIN_0013 + 64 <= bv_unsigned wo.
  Hypothesis Hlen : length row = 296%nat.
  Hypothesis Hp8 : bv_unsigned wp mod 8 = 0.
  Hypothesis DRS : bv_unsigned sp <= bv_unsigned wp \/ bv_unsigned wp + 296 <= bv_unsigned sp - 112.
  Hypothesis DRO : bv_unsigned wo + 32 <= bv_unsigned wp \/ bv_unsigned wp + 296 <= bv_unsigned wo.
  Hypothesis HNO : (bv_unsigned wb = 5 \/ bv_unsigned wb = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 112) /\
    (bv_unsigned wo + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned wo).
  Hypothesis HRB0 : bytes_at rsegs m (bv_unsigned wp) row.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 112) (bv_unsigned sp).
  Hypothesis HOC0 : rw_cells rsegs m (bv_unsigned wo) [CB 32 ob].
  Hypothesis MI0 : mem_inv rsegs m.

  Definition Q := reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m
    (bv_unsigned wp) (bv_unsigned wb) (bv_unsigned wo) row nb.

  (* The frame: 40 bytes of locals, then the saved s3, s2, s1, s0, ra. *)
  Definition FR (m' : word -> option byte) (j : list byte) : Prop :=
    rw_cells rsegs m' (bv_unsigned sp + -80) [CB 40 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition FS (m' : word -> option byte) : Prop :=
    stk rsegs m' (bv_unsigned sp - 112) (bv_unsigned sp + -80) /\
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned wo, bv_unsigned wo + 32)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m'.

  Definition R0 (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) :=
    mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3'
        s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'.

  Definition at_ (pc : Z) (R : bvmap 5 word) (m' : word -> option byte) : machine_state :=
    MS R F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs).

  Lemma mb_row : forall m', FS m' -> bytes_at rsegs m' (bv_unsigned wp) row.
  Proof.
    intros m' (_ & MU & _). eapply bytes_at_transport; [exact HRB0 | exact MU | rewrite Hlen; dj].
  Qed.

  (* After a callee whose footprint W lies inside ours and spares the frame. *)
  Lemma mb_call : forall W m' m'' j, FR m' j -> FS m' -> munch W m' m'' -> wmono rsegs m' m'' -> mem_inv rsegs m'' ->
    disjoint_from W (bv_unsigned sp + -80) 80 ->
    sub_fp W [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned wo, bv_unsigned wo + 32)] ->
    stk rsegs m'' (bv_unsigned sp - 112) (bv_unsigned sp + -80) ->
    FR m'' j /\ FS m''.
  Proof.
    intros W m' m'' j HF (ST & MU & WM & MI) MU2 WM2 MI2 D S ST2. split.
    - eapply rw_cells_transport; [exact HF | exact MU2 | exact WM2 | exact D].
    - split; [exact ST2|]. split; [eapply munch_trans; [exact MU | eapply munch_weaken; [exact S | exact MU2]]|].
      split; [eapply wmono_trans; eassumption | exact MI2].
  Qed.

  Lemma epi : forall (r : Z) X ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    FR m' j -> FS m' -> bytes_at rsegs m' (bv_unsigned wo) X -> X = synth row (bv_unsigned wb) nb ->
    r = rc row (bv_unsigned wb) ->
    evt rsegs Q (at_ 0x14eb0 (R0 ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 r) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros r X ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j
      HF (ST & MU & WM & MI) HX EX Er. subst r X. unfold at_, R0, FR in *.
    do 8 step.
    apply evt_done. unfold Q, reac_box_model_block_post.
    replace ((bv_unsigned wp =? 0) || (bv_unsigned wo =? 0)) with false
      by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    do 15 eexists. split; [reflexivity|].
    split; [split; [exact HX | exact MU]|].
    split; [exact WM|]. split; [exact MI|].
    pose proof (stk_release rsegs m' _ _ _ ST HF ltac:(lia)) as STf. cbn [cells_size csize Nat.add] in STf.
    apply (mb_stk_hi _ _ _ _ _ STf). lia.
  Qed.

  Lemma fin : forall X ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    FR m' j -> FS m' -> bytes_at rsegs m' (bv_unsigned wo) X -> X = synth row (bv_unsigned wb) nb ->
    rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14eac (R0 ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros X ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j HF HS HX EX Er.
    unfold at_, R0. step.
    eapply (epi 1); [exact HF | exact HS | exact HX | exact EX | symmetry; exact Er].
  Qed.

  Lemma call_mc : forall (ret : Z) (k n : nat) (A : Z) Sb X (a0 a1 a2 : word)
      t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (k + n <= 32)%nat -> length Sb = n ->
    bv_unsigned a0 = bv_unsigned wo + Z.of_nat k -> bv_unsigned a1 = A -> bv_unsigned a2 = Z.of_nat n ->
    (A + Z.of_nat n <= bv_unsigned wo + Z.of_nat k \/ bv_unsigned wo + Z.of_nat k + Z.of_nat n <= A) ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] -> bytes_at rsegs m' A Sb ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       FR m'' j -> FS m'' ->
       munch [(bv_unsigned wo + Z.of_nat k, bv_unsigned wo + Z.of_nat k + Z.of_nat n)] m' m'' ->
       wmono rsegs m' m'' -> rw_cells rsegs m'' (bv_unsigned wo) [CB 32 (upd_bytes X k Sb)] ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' s0' s1' a0 a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1d344) fc None m' (seg_rom rsegs)).
  Proof.
    intros ret k n A Sb X a0 a1 a2 t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j Hret Hkn LS
      E0 E1 E2 DSO HF HS HO HSb K.
    pose proof HS as (ST & MU & WM & MI).
    pose proof (rs_rw_sub rsegs m' _ 32 X k n HO Hkn) as HSub.
    unfold R0. eapply evt_cut.
    { eapply HMC; [ | | | | exact MI].
      - rewrite E1. exact HSb.
      - rewrite E2, Nat2Z.id. exact LS.
      - rewrite E0, E2, Nat2Z.id. exact HSub.
      - rewrite E0, E1, E2. lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2 & RW2 & SB2).
    subst ms'. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. clear SB2.
    pose proof (rs_rw_upd rsegs m' m2 _ 32 X k n _ HO Hkn MU2 WM2 RW2) as HO2.
    destruct (mb_call _ m' m2 j HF HS MU2 WM2 MI2 ltac:(dj) ltac:(sfp)
                (stk_transport_disjoint rsegs _ m' m2 _ _ ST MU2 WM2 ltac:(dj))) as [HF2 HS2].
    rewrite Hret. exact (K u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 HF2 HS2 MU2 WM2 HO2).
  Qed.

  Lemma case_join : forall (A : Z) JJ ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    bytes_at rsegs m' A JJ -> length JJ = 32%nat -> (bv_unsigned wo + 32 <= A \/ A + 32 <= bv_unsigned wo) ->
    JJ = synth row (bv_unsigned wb) nb -> rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14bb4 (R0 ra' t0' t1' t2' wo wp a0' (Z_to_bv 64 A) a2' a3' a4' a5' a6' a7'
                                 (Z_to_bv 64 (-1)) s3' t3' t4' t5' t6') m').
  Proof.
    intros A JJ ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j HF HS HO HJ LJ DJ EJ Er.
    pose proof (bytes_at_bound _ _ _ _ HJ) as BJ. rewrite LJ in BJ.
    unfold at_, R0. step. step. step.
    eapply (call_mc 0x14bc0 0 32 A JJ (zeros 32)); [apply ret_pc_even; [lia | reflexivity] | lia | exact LJ
           | rewrite Z.add_0_r; reflexivity | rewrite unsigned_lit; lia | rewrite unsigned_lit; lia | lia
           | exact HF | exact HS | exact HO | exact HJ |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m'' HF2 HS2 _ _ HO2.
    unfold at_, R0. step.
    eapply fin; [exact HF2 | exact HS2 | exact (mb_rw1 _ _ _ _ _ HO2) | | exact Er].
    rewrite <- EJ. unfold upd_bytes. rewrite LJ. change (firstn 0 (zeros 32)) with (@nil byte).
    change (skipn (0 + 32) (zeros 32)) with (@nil byte). rewrite app_nil_r. reflexivity.
  Qed.

  Lemma case1 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 1 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14bac (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof HS as (_ & _ & _ & MI).
    unfold at_, R0. step. step.
    eapply (case_join 0x10634 J14); [exact HF | exact HS | exact HO | | reflexivity | unfold JOIN_0013 in DOJ; lia
           | rewrite Hb; reflexivity | rewrite Hb; reflexivity].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.

  Lemma case2 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 2 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14b80 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof HS as (_ & _ & _ & MI).
    unfold at_, R0. step. step. step.
    eapply (case_join 0x10614 J13); [exact HF | exact HS | exact HO | | reflexivity | unfold JOIN_0013 in DOJ; lia
           | rewrite Hb; reflexivity | rewrite Hb; reflexivity].
    apply rc_ro_in_image; [exact MI | vm_compute; reflexivity].
  Qed.

  (* build_dt1_single (wo, a1, D at the frame's offset 3, |D|), then the tail at 0x14eac. *)
  Lemma call_bd : forall (D : list byte) (a0w a1w a2w a3w : word) t0 t1 t2 s1' a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j,
    bv_unsigned a0w = bv_unsigned wo -> bv_unsigned a2w = bv_unsigned sp - 77 ->
    bv_unsigned a3w = Z.of_nat (length D) -> (length D <= 9)%nat ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    bytes_at rsegs m' (bv_unsigned sp - 77) D ->
    synth row (bv_unsigned wb) nb = dt1_out (length D) (bv_unsigned a1w) D (zeros 32) ->
    rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 0x14eac) t0 t1 t2 wo s1' a0w a1w a2w a3w a4 a5 a6 a7 s2' s3' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15040) fc None m' (seg_rom rsegs)).
  Proof.
    intros D a0w a1w a2w a3w t0 t1 t2 s1' a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j E0 E2 E3 L9 HF HS HO HD ES Er.
    pose proof HS as (ST & MU & WM & MI).
    pose proof (bytes_at_bound _ _ _ _ HD) as BD.
    assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80)
      by (rewrite unsigned_lit; lia).
    pose proof HBD as HB0. unfold build_dt1_single_contract, BUILD_DT1_SINGLE in HB0.
    unfold R0. eapply evt_cut.
    { eapply HB0 with (ob := zeros 32) (D := D).
      - rewrite Usp. replace (bv_unsigned sp + -80 - 32) with (bv_unsigned sp - 112) by lia. exact ST.
      - lia.
      - lia.
      - lia.
      - rewrite E0. exact HO.
      - lia.
      - lia.
      - rewrite E2. exact HD.
      - lia.
      - rewrite Usp. lia.
      - rewrite Usp. lia.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & HB2 & _ & _
                    & MU2 & WM2 & MI2 & ST2).
    subst ms'. rewrite Usp in MU2, ST2. rewrite E0, E3 in MU2. rewrite E0, E3, Nat2Z.id in HB2.
    replace (bv_unsigned sp + -80 - 32) with (bv_unsigned sp - 112) in MU2, ST2 by lia.
    destruct (mb_call _ m' m2 j HF HS MU2 WM2 MI2 ltac:(dj) ltac:(sfp) ST2) as [HF2 HS2].
    replace (ret_pc (Z_to_bv 64 0x14eac)) with (Z_to_bv 64 0x14eac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply fin; [exact HF2 | exact HS2 | exact HB2 | symmetry; exact ES | exact Er].
  Qed.

  (* A callee wrote Y at the frame's offset k and nothing else of the frame. *)
  Lemma mb_fr_upd : forall W m' m'' j k n Y,
    FR m' j -> (k + n <= 40)%nat -> munch W m' m'' -> wmono rsegs m' m'' ->
    disjoint_from W (bv_unsigned sp + -80) (Z.of_nat k) ->
    disjoint_from W (bv_unsigned sp + -80 + Z.of_nat (k + n)) (Z.of_nat (80 - (k + n))) ->
    bytes_at rsegs m'' (bv_unsigned sp + -80 + Z.of_nat k) Y -> length Y = n ->
    FR m'' (upd_bytes j k Y).
  Proof.
    intros W m' m'' j k n Y HF Hkn MU WM D1 D2 HY LY. unfold FR in *.
    pose proof HF as [[[Lj Hcs] _] _]. cbn [cell_wf] in Lj.
    apply mb_flat in HF. cbn [cells_size csize Nat.add] in HF.
    pose proof (mb_upd rsegs m' m'' _ 80 _ k n Y W HF ltac:(lia) MU WM D1 D2 HY LY) as H2.
    rewrite mb_upd_app in H2 by lia.
    apply (mb_unflat _ _ _ 40); [exact H2 | rewrite upd_bytes_length by lia; lia | exact Hcs].
  Qed.

  (* name_field (p, frame + k): the frame's 16 bytes at k become nmr row nb. *)
  Lemma call_nf : forall (k : nat) (ret : Z) X (a0w a1w : word) t0 t1 t2 s1' a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (k + 16 <= 40)%nat ->
    bv_unsigned a0w = bv_unsigned wp -> bv_unsigned a1w = bv_unsigned sp + -80 + Z.of_nat k ->
    (bv_unsigned wb = 5 \/ bv_unsigned wb = 6) -> has row <> 0 ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       FR m'' (upd_bytes j k (nmr row nb)) -> FS m'' -> rw_cells rsegs m'' (bv_unsigned wo) [CB 32 X] ->
       bytes_at rsegs m'' (bv_unsigned sp + -80 + Z.of_nat k) (nmr row nb) -> length (nmr row nb) = 16%nat ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' wo s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 wo s1' a0w a1w a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1525c) fc None m' (seg_rom rsegs)).
  Proof.
    intros k ret X a0w a1w t0 t1 t2 s1' a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j Hret Hk E0 E1 B56 Hh HF HS HO K.
    pose proof HS as (ST & MU & WM & MI).
    pose proof (mb_row m' HS) as HR.
    pose proof (bytes_at_bound _ _ _ _ HR) as BR.
    pose proof (rs_rw64_range row 280) as RN.
    assert (Usp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80)
      by (rewrite unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 (rname row)) = rname row) by (rewrite unsigned_lit; unfold rname; lia).
    assert (HN8 : bytes_at rsegs m' (bv_unsigned wp + 280) (le8 (Z_to_bv 64 (rname row)))).
    { unfold rname. rewrite rs_le8 by lia. exact (bytes_at_sub rsegs m' _ row 280 8 HR ltac:(lia)). }
    pose proof HF as HF0. unfold FR in HF0. apply mb_flat in HF0. cbn [cells_size csize Nat.add] in HF0.
    pose proof (rs_rw_sub rsegs m' _ 80 _ k 16 HF0 ltac:(lia)) as HBUF.
    rewrite <- E1 in HBUF.
    assert (HNB : exists nb', ((bv_unsigned (Z_to_bv 64 (rname row)) = 0 /\ nb' = []) \/
                   (bv_unsigned (Z_to_bv 64 (rname row)) <> 0 /\ name_ok nb' /\
                    bv_unsigned (Z_to_bv 64 (rname row)) + Z.of_nat (length nb') <= 2^64 /\
                    bytes_at rsegs m' (bv_unsigned (Z_to_bv 64 (rname row))) nb')) /\
                  (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb') <= bv_unsigned sp - 112) /\
                  (bv_unsigned wo + 32 <= rname row \/ rname row + Z.of_nat (length nb') <= bv_unsigned wo) /\
                  (length nb' <= 16)%nat /\ nmf nb' = nmr row nb).
    { rewrite UN. unfold nmr. destruct (Z.eqb_spec (rname row) 0) as [Z0|NZ].
      - exists []. split; [left; split; [exact Z0 | reflexivity]|]. cbn [length Z.of_nat].
        split; [lia|]. split; [lia|]. split; [lia | reflexivity].
      - exists nb. destruct (HNO B56 Hh NZ) as (OK & HB & D1 & D2).
        pose proof (bytes_at_bound _ _ _ _ HB) as BB. pose proof OK as (OKl & _ & _).
        split; [right; split; [exact NZ|]; split; [exact OK|]; split; [lia|]|].
        + eapply bytes_at_transport; [exact HB | exact MU | dj].
        + split; [exact D1|]. split; [exact D2|]. split; [lia | reflexivity]. }
    destruct HNB as (nb' & HNB & DN1 & DN2 & LNB & ENM).
    assert (LN : length (nmr row nb) = 16%nat) by (rewrite <- ENM; apply mb_nmf_len; exact LNB).
    pose proof HNF as HN0. unfold name_field_contract, NAME_FIELD in HN0.
    unfold R0. eapply evt_cut.
    { eapply HN0 with (name := Z_to_bv 64 (rname row)) (nb := nb').
      - rewrite Usp. replace (bv_unsigned sp + -80 - 32) with (bv_unsigned sp - 112) by lia. exact ST.
      - lia.
      - rewrite E0. exact Hp8.
      - lia.
      - rewrite E0. exact HN8.
      - lia.
      - exact HBUF.
      - exact HNB.
      - rewrite Usp, E0. lia.
      - rewrite Usp, UN. lia.
      - rewrite Usp, E1. lia.
      - rewrite E0, E1. lia.
      - rewrite E1, UN. lia.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & HB2
                    & MU2 & WM2 & MI2 & ST2).
    subst ms'. rewrite Usp in MU2, ST2. rewrite E1 in HB2, MU2. rewrite ENM in HB2.
    replace (bv_unsigned sp + -80 - 32) with (bv_unsigned sp - 112) in MU2, ST2 by lia.
    pose proof (mb_fr_upd _ m' m2 j k 16 _ HF Hk MU2 WM2 ltac:(dj) ltac:(dj) HB2 LN) as HF2.
    assert (HS2 : FS m2).
    { split; [exact ST2|]. split; [eapply munch_trans; [exact MU | (eapply munch_weaken; [ | exact MU2]); sfp]|].
      split; [eapply wmono_trans; eassumption | exact MI2]. }
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ HO MU2 WM2 ltac:(dj)) as HO2.
    rewrite Hret. apply K; assumption.
  Qed.

  (* 0x14dd0: the outer check byte, then the tail at 0x14eac. *)
  Lemma sum_tail : forall X ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    length X = 32%nat -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    withchk (firstn 31 X) = synth row (bv_unsigned wb) nb -> rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14dd0 (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum X 31)) a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros X ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j LX HF HS HO ES Er.
    destruct HS as (ST & MU & WM & MI). unfold FR in HF. unfold at_, R0.
    step. bstep. step. step. step.
    destruct HO as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
    eapply fin; [exact HF | exact (conj ST (conj MU (conj WM MI))) | exact HB | | exact Er].
    rewrite <- ES. unfold withchk, chk. rewrite rs_negw8, rs_psum_firstn by lia. reflexivity.
  Qed.

  (* The outer sum of build_ident_first, at 0x14c2c. *)
  Lemma loop5 : forall k i X (a2w : word) ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> length X = 32%nat ->
    bv_unsigned a2w = 18446744073709551615 - bv_unsigned wo ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    withchk (firstn 31 X) = synth row (bv_unsigned wb) nb -> rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14c2c (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a2w
                                 (Z_to_bv 64 31) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros i X a2w ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hik Hk LX H2 HF HS HO ES Er; [lia|].
    pose proof (rd_byte rsegs m' (bv_unsigned wo) X i (mb_rw1 _ _ _ _ _ HO) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    bstep.
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      replace (S i) with 31%nat by lia.
      eapply sum_tail; [exact LX | exact HF | exact HS | exact HO | exact ES | exact Er].
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* The outer sum of build_ident_last, at 0x14db8. *)
  Lemma loop6 : forall k i X (a2w : word) ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> length X = 32%nat ->
    bv_unsigned a2w = 18446744073709551615 - bv_unsigned wo ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    withchk (firstn 31 X) = synth row (bv_unsigned wb) nb -> rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14db8 (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a2w
                                 (Z_to_bv 64 31) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros i X a2w ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hik Hk LX H2 HF HS HO ES Er; [lia|].
    pose proof (rd_byte rsegs m' (bv_unsigned wo) X i (mb_rw1 _ _ _ _ _ HO) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    bstep.
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      eapply sum_tail; [exact LX | exact HF | exact HS | exact HO | exact ES | exact Er].
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* 0x14d84: the inner check byte and the f7 of build_ident_last, then its outer sum. *)
  Lemma tail6 : forall X REC ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    length X = 32%nat -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    0 <= psum REC 21 < 2^31 ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) =
      synth row (bv_unsigned wb) nb ->
    rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14d84 (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum REC 21)) a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros X REC ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j LX HF HS HO PR ES Er.
    destruct HS as (ST & MU & WM & MI). unfold FR in HF. unfold at_, R0.
    step. bstep. step. step. step. step. bstep.
    step. step. step. step. step. step.
    apply (rs_rw_take _ _ _ _ 4) in HO.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HO.
    rewrite mb_stamp8 in HO.
    match type of HO with rw_cells _ _ _ [CB 32 ?X6] =>
      replace X6 with (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]) in HO end.
    2:{ unfold upd_bytes. rewrite skipn_skipn. cbn [length Nat.add app]. rewrite ?app_nil_r.
        f_equal. apply mb_cons; [reflexivity|]. apply mb_cons; [apply Z_to_bv8_mod; vm_compute; reflexivity|].
        reflexivity. }
    eapply (loop6 31 0 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]));
      [lia | lia | rewrite upd_bytes_length; cbn [length]; lia | | exact HF
      | exact (conj ST (conj MU (conj WM MI))) | exact HO | exact ES | exact Er].
    rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. reflexivity.
  Qed.

  (* The inner sum of build_ident_last over rec (the frame's bytes 3..23), at 0x14d74. *)
  Lemma loopr : forall k i REC X ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (i + k = 21)%nat -> (0 < k)%nat -> length REC = 21%nat -> length X = 32%nat ->
    bytes_at rsegs m' (bv_unsigned sp - 77) REC ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) =
      synth row (bv_unsigned wb) nb ->
    rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x14d74 (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum REC i))
                                 (Z_to_bv 64 (bv_unsigned sp - 77 + Z.of_nat i))
                                 (Z_to_bv 64 (bv_unsigned sp + -56)) a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros i REC X ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hik Hk LR LX HREC HF HS HO ES Er; [lia|].
    pose proof (rd_byte rsegs m' (bv_unsigned sp - 77) REC i HREC ltac:(lia)) as RD.
    pose proof (psum_range REC i) as PR.
    unfold at_, R0.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (bv_unsigned sp - 77 + Z.of_nat i + 1) (bv_unsigned sp + -56)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned sp - 77 + Z.of_nat i + 1 =? bv_unsigned sp + -56) with true
        by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by lia.
      eapply tail6; [exact LX | exact HF | exact HS | exact HO | pose proof (psum_range REC 21); lia | exact ES
        | exact Er].
    - replace (bv_unsigned sp - 77 + Z.of_nat i + 1 =? bv_unsigned sp + -56) with false
        by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (bv_unsigned sp - 77 + Z.of_nat i + 1) with (bv_unsigned sp - 77 + Z.of_nat (S i)) by lia.
      eapply (IH (S i)); [lia | lia | exact LR | exact LX | exact HREC | exact HF | exact HS | exact HO | exact ES
        | exact Er].
  Qed.

  (* memcpy within the frame: offset k <- A, n bytes. *)
  Lemma call_mcf : forall (ret : Z) (k n : nat) (A : Z) Sb X (a0 a1 a2 : word)
      t0 t1 t2 s1' a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j,
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> (k + n <= 40)%nat -> length Sb = n ->
    bv_unsigned a0 = bv_unsigned sp + -80 + Z.of_nat k -> bv_unsigned a1 = A -> bv_unsigned a2 = Z.of_nat n ->
    (A + Z.of_nat n <= bv_unsigned sp + -80 + Z.of_nat k \/ bv_unsigned sp + -80 + Z.of_nat k + Z.of_nat n <= A) ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] -> bytes_at rsegs m' A Sb ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'',
       FR m'' (upd_bytes j k Sb) -> FS m'' -> rw_cells rsegs m'' (bv_unsigned wo) [CB 32 X] ->
       munch [(bv_unsigned sp + -80 + Z.of_nat k, bv_unsigned sp + -80 + Z.of_nat k + Z.of_nat n)] m' m'' ->
       bytes_at rsegs m'' (bv_unsigned sp + -80 + Z.of_nat k) Sb ->
       evt rsegs Q (at_ ret (R0 (Z_to_bv 64 ret) t0' t1' t2' wo s1' a0 a1' a2' a3' a4' a5' a6' a7' s2' s3'
                                t3' t4' t5' t6') m'')) ->
    evt rsegs Q (MS (R0 (Z_to_bv 64 ret) t0 t1 t2 wo s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1d344) fc None m' (seg_rom rsegs)).
  Proof.
    intros ret k n A Sb X a0 a1 a2 t0 t1 t2 s1' a3 a4 a5 a6 a7 s2' s3' t3 t4 t5 t6 m' j Hret Hkn LS
      E0 E1 E2 DSO HF HS HO HSb K.
    pose proof HS as (ST & MU & WM & MI).
    pose proof HF as HF0. unfold FR in HF0. apply mb_flat in HF0. cbn [cells_size csize Nat.add] in HF0.
    pose proof (rs_rw_sub rsegs m' _ 80 _ k n HF0 ltac:(lia)) as HSub.
    unfold R0. eapply evt_cut.
    { eapply HMC; [ | | | | exact MI].
      - rewrite E1. exact HSb.
      - rewrite E2, Nat2Z.id. exact LS.
      - rewrite E0, E2, Nat2Z.id. exact HSub.
      - rewrite E0, E1, E2. lia. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2
                    & RW2 & SB2).
    subst ms'. rewrite E0, E2, Nat2Z.id in RW2. rewrite E0, E2 in MU2. clear SB2.
    pose proof (mb_rw1 _ _ _ _ _ RW2) as HB2.
    pose proof (mb_fr_upd _ m' m2 j k n Sb HF Hkn MU2 WM2 ltac:(dj) ltac:(dj) HB2 LS) as HF2.
    assert (HS2 : FS m2).
    { split; [eapply stk_transport_disjoint; [exact ST | exact MU2 | exact WM2 | dj]|].
      split; [eapply munch_trans; [exact MU | (eapply munch_weaken; [ | exact MU2]); sfp]|].
      split; [eapply wmono_trans; eassumption | exact MI2]. }
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ HO MU2 WM2 ltac:(dj)) as HO2.
    rewrite Hret. apply K; assumption.
  Qed.

  (* build_config: the 8 header bytes. *)
  Definition H8 : list byte := [bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row].

  Lemma ok0 : forall m' X k, (k < 32)%nat -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    store_ok rsegs m' (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) 1 = true.
  Proof.
    intros m' X k Hk [_ HW]. cbn [cells_size csize Nat.add] in HW.
    exact (wr_at_store_ok rsegs m' _ _ (Z.of_nat k) 1 HW ltac:(lia) ltac:(lia)).
  Qed.

  (* A byte store at a variable offset k of the output block. *)
  Lemma ost0 : forall m' j X k v, (k < 32)%nat -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    FR (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) (le1 v)) j /\
    FS (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) (le1 v)) /\
    rw_cells rsegs (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) (le1 v)) (bv_unsigned wo)
      [CB 32 (upd_bytes X k [Z_to_bv 8 (bv_unsigned v)])].
  Proof.
    intros m' j X k v Hk HF (ST & MU & WM & MI) HO.
    pose proof (ok0 m' X k Hk HO) as HS1.
    pose proof HO as [[[LX _] HB] HW]. cbn [cell_wf] in LX. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    cbn [cells_size csize Nat.add] in HW.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
    change (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) with (wa (bv_unsigned wo + Z.of_nat k)) in *.
    split.
    { unfold FR in *. apply rw_cells_frame; [exact HF | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]. }
    split.
    { split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
      split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; split; lia]|].
      split; [apply wmono_write; exact WM|]. apply mem_inv_store; [exact MI | exact HS1]. }
    split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite upd_bytes_length by (cbn [length]; lia); exact LX | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      pose proof (bytes_at_write_inside rsegs m' _ X (Z.of_nat k) [Z_to_bv 8 (bv_unsigned v)] HB ltac:(lia)
                    ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H. rewrite Nat2Z.id in H. exact H.
    - cbn [cells_size csize Nat.add]. apply wr_at_write. exact HW.
  Qed.

  (* One step that stores a byte at offset k of the output block. *)
  Ltac vst_ k HF HS HO :=
    lazymatch type of HO with rw_cells rsegs ?mm (bv_unsigned wo) [CB 32 ?X] =>
    lazymatch type of HF with FR mm ?jj =>
      let HSo := fresh "HSo" in
      pose proof (ok0 mm X k ltac:(lia) HO) as HSo;
      step; clear HSo;
      lazymatch goal with |- context [write_to_mem mm (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) (le1 ?v)] =>
        let HF' := fresh "HF" in let HS' := fresh "HS" in let HO' := fresh "HO" in
        destruct (ost0 mm jj X k v ltac:(lia) HF HS HO) as (HF' & HS' & HO'); clear HF HS HO;
        let m2 := fresh "m" in
        set (m2 := write_to_mem mm (Z_to_bv 64 (bv_unsigned wo + Z.of_nat k)) (le1 v)) in *; clearbody m2;
        rename HF' into HF; rename HS' into HS; rename HO' into HO
      end end end.
  Tactic Notation "vst" constr(k) := match goal with
    | HF : FR _ _, HS : FS _, HO : rw_cells rsegs _ (bv_unsigned wo) [CB 32 _] |- _ => vst_ k HF HS HO end.

  (* The outer sum of build_config, at 0x15020. *)
  Lemma loop0 : forall k i X (a2w : word) ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (i + k = 31)%nat -> (0 < k)%nat -> length X = 32%nat ->
    bv_unsigned a2w = 18446744073709551615 - bv_unsigned wo ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 X] ->
    withchk (firstn 31 X) = synth row (bv_unsigned wb) nb -> rc row (bv_unsigned wb) = 1 ->
    evt rsegs Q (at_ 0x15020 (R0 ra' t0' t1' t2' wo s1' (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a2w
                                 (Z_to_bv 64 31) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros i X a2w ra' t0' t1' t2' s1' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hik Hk LX H2 HF HS HO ES Er; [lia|].
    pose proof (rd_byte rsegs m' (bv_unsigned wo) X i (mb_rw1 _ _ _ _ _ HO) ltac:(lia)) as RD.
    pose proof (psum_range X i) as PR.
    unfold at_, R0.
    bstep.
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      eapply sum_tail; [exact LX | exact HF | exact HS | exact HO | exact ES | exact Er].
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* 0x14fec: the tail bytes, then the outer sum. *)
  Lemma tailc : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ slots row ++ zeros 12)] ->
    evt rsegs Q (at_ 0x14fec (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j Hb Hsy HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_slots_len row Hsy) as LS.
    assert (LT : length (tail row) = 11%nat) by (unfold tail; rewrite length_firstn, length_skipn, Hlen; reflexivity).
    unfold at_, R0. step. bstep. step. step. bstep. step. step. step. step.
    eapply (call_mc 0x15010 20 11 (bv_unsigned wp + 254) (tail row)); [apply ret_pc_even; [lia | reflexivity] | lia
      | exact LT | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | lia
      | exact HF | exact HS | exact HO | |].
    { pose proof (bytes_at_sub _ _ _ _ 254 11 HR ltac:(lia)) as H.
      apply (bytes_at_addr _ _ _ (bv_unsigned wp + 254)) in H; [exact H | lia]. }
    intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 HF2 HS2 _ _ HO2.
    unfold at_, R0. step. step. step. step.
    assert (LX : length (H8 ++ slots row ++ zeros 12) = 32%nat)
      by (rewrite !length_app, LS; unfold zeros; rewrite repeat_length; reflexivity).
    eapply (loop0 31 0 (upd_bytes (H8 ++ slots row ++ zeros 12) 20 (tail row)));
      [lia | lia | rewrite upd_bytes_length; [exact LX | rewrite LX, LT; lia] | | exact HF2 | exact HS2 | exact HO2 | |].
    - rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. reflexivity.
    - rewrite Hb, mb_synth0, Hsy.
      rewrite (rs_upd_fill H8 (slots row) (tail row) 12 20) by (rewrite ?LS, ?LT; first [reflexivity | lia]).
      rewrite LT. change (12 - 11)%nat with 1%nat. rewrite app_assoc.
      assert (L : length (H8 ++ slots row ++ tail row) = 31%nat) by (rewrite !length_app, LS, LT; reflexivity).
      rewrite <- L at 1. rewrite firstn_app_exact.
      change (H8 ++ slots row ++ tail row) with (gram31 row).
      unfold gram, withchk, chk. rewrite rs_gram_chk. reflexivity.
    - rewrite Hb, mb_rc0, Hsy. reflexivity.
  Qed.

  (* The fill loop of empty slots (3), at 0x14fd8. *)
  Lemma fill : forall k P (a0w : word) ra' t0' t1' t2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (length P + k = 12)%nat -> (0 < k)%nat -> P ++ repeat (bz 3) k = slots row ->
    bv_unsigned a0w = 18446744073709551615 - bv_unsigned wo ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14fd8 (R0 ra' t0' t1' t2' wo wp a0w (Z_to_bv 64 3) (Z_to_bv 64 (Z.of_nat (8 + length P)))
                                 (Z_to_bv 64 20) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros P a0w ra' t0' t1' t2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hk Hk0 EP H0w Hb Hsy HF HS HO; [lia|].
    unfold at_, R0.
    bstep. step. step.
    vst (8 + length P)%nat.
    step.
    rewrite (rc_eqb_lit (Z.of_nat (8 + length P) + 1) 20) by lia.
    rewrite mb_fill_step in HO by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 3))) with (bz 3) in HO.
    destruct k as [|k].
    - replace (Z.of_nat (8 + length P) + 1 =? 20) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      replace (P ++ [bz 3]) with (slots row) in HO by (rewrite <- EP; reflexivity).
      rewrite (rs_slots_len row Hsy) in HO. change (24 - 12)%nat with 12%nat in HO.
      eapply tailc; [exact Hb | exact Hsy | exact HF | exact HS | exact HO].
    - replace (Z.of_nat (8 + length P) + 1 =? 20) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      replace (Z_to_bv 64 (Z.of_nat (8 + length P) + 1)) with (Z_to_bv 64 (Z.of_nat (8 + length (P ++ [bz 3]))))
        by (f_equal; rewrite length_app; cbn [length]; lia).
      eapply (IH (P ++ [bz 3])); [rewrite length_app; cbn [length]; lia | lia | rewrite <- EP, <- app_assoc; reflexivity
        | exact H0w | exact Hb | exact Hsy | exact HF | exact HS | exact HO].
  Qed.

  (* 0x14fb4: the fill loop's entry. *)
  Lemma at_dd8 : forall P ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (length P <= 12)%nat -> P ++ repeat (bz 3) (12 - length P) = slots row ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14fb4 (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat (length P))) a1' a2' a3' a4' a5' a6' a7'
                                 s2' s3' t3' t4' t5' t6') m').
  Proof.
    intros P ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j LP EP Hb Hsy HF HS HO.
    unfold at_, R0.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    step. step. rewrite mb_lts_lit by lia.
    destruct (Z.ltb_spec 11 (Z.of_nat (length P))) as [C|C]; cbv iota.
    - assert (L12 : length P = 12%nat) by lia. rewrite L12 in EP, HO.
      change (12 - 12)%nat with 0%nat in EP. cbn [repeat] in EP. rewrite app_nil_r in EP.
      rewrite EP in HO. change (24 - 12)%nat with 12%nat in HO.
      eapply tailc; [exact Hb | exact Hsy | exact HF | exact HS | exact HO].
    - step. step. step. step. step. step.
      rewrite mb_zext32 by lia.
      replace (Z_to_bv 64 (Z.of_nat (length P) + 8)) with (Z_to_bv 64 (Z.of_nat (8 + length P))) by (f_equal; lia).
      eapply (fill (12 - length P) P); [lia | lia | exact EP | rewrite zb_lxor_ones by lia; rewrite unsigned_lit by lia; reflexivity
        | exact Hb | exact Hsy | exact HF | exact HS | exact HO].
  Qed.

  (* lay = 1: the input slots (0), at 0x14f24. *)
  Lemma l2a : forall k P ra' t0' t1' t2' a2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (length P + k <= 12)%nat -> (0 < k)%nat -> P ++ repeat (bz 0) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14f24 (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 2147483640) a2'
                                 (Z_to_bv 64 (Z.of_nat k)) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros P ra' t0' t1' t2' a2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hk Hk0 EP Hb Hsy HF HS HO; [lia|].
    unfold at_, R0.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by lia.
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (Z.of_nat (S k) + -1) 0) by lia.
    rewrite mb_fill_step in HO by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))) with (bz 0) in HO.
    replace (Z_to_bv 64 (Z.of_nat (length P) + 1)) with (Z_to_bv 64 (Z.of_nat (length (P ++ [bz 0]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    destruct k as [|k].
    - replace (Z.of_nat 1 + -1 =? 0) with true by reflexivity. cbv iota.
      eapply (at_dd8 (P ++ [bz 0])); [rewrite length_app; cbn [length]; lia | | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      eapply (IH (P ++ [bz 0])); [rewrite length_app; cbn [length]; lia | lia | | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay <> 1: the output slots (1), at 0x14f7c. *)
  Lemma l2b : forall k P ra' t0' t1' t2' a3' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    (length P + k <= 12)%nat -> (0 < k)%nat -> P ++ repeat (bz 1) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14f7c (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 2147483640)
                                 (Z_to_bv 64 1) a3' (Z_to_bv 64 (Z.of_nat k)) a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros P ra' t0' t1' t2' a3' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j
      Hk Hk0 EP Hb Hsy HF HS HO; [lia|].
    unfold at_, R0.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by lia.
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (Z.of_nat (S k) + -1) 0) by lia.
    rewrite mb_fill_step in HO by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HO.
    replace (Z_to_bv 64 (Z.of_nat (length P) + 1)) with (Z_to_bv 64 (Z.of_nat (length (P ++ [bz 1]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    destruct k as [|k].
    - replace (Z.of_nat 1 + -1 =? 0) with true by reflexivity. cbn [negb]. cbv iota.
      eapply (at_dd8 (P ++ [bz 1])); [rewrite length_app; cbn [length]; lia | | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      eapply (IH (P ++ [bz 1])); [rewrite length_app; cbn [length]; lia | lia | | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay = 1, after the output slots: 0x14f10. *)
  Lemma at_d34 : forall P ra' t0' t1' t2' a2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    lay row = 1 -> P = repeat (bz 1) (Z.to_nat (oc row / 4)) -> bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14f10 (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 (ic row)) a2'
                                 (Z_to_bv 64 (ic row / 4)) a4' a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    intros P ra' t0' t1' t2' a2' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j L1 EP Hb Hsy HF HS HO.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro & Mi & Mo & Sum).
    pose proof (rs_ic_range row) as RI.
    assert (LP : length P = Z.to_nat (oc row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 0) (Z.to_nat (ic row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (ic row / 4)))).
    { rewrite (rs_slots_1 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (oc row / 4) + Z.to_nat (ic row / 4)))%nat by lia. reflexivity. }
    unfold at_, R0.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - eapply at_dd8; [rewrite LP; lia | | exact Hb | exact Hsy | exact HF | exact HS | exact HO].
      rewrite ES, I0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. rewrite rs_seqz by lia. step. step.
      replace (Z_to_bv 64 (ic row / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (ic row / 4)))) by (f_equal; lia).
      eapply (l2a (Z.to_nat (ic row / 4)) P); [lia | lia | symmetry; exact ES | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
  Qed.

  (* lay <> 1, after the input slots: 0x14f64. *)
  Lemma at_d88 : forall P ra' t0' t1' t2' a1' a3' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j,
    lay row <> 1 -> P = repeat (bz 2) (Z.to_nat (ic row / 4)) -> bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14f64 (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat (length P))) a1' (Z_to_bv 64 (oc row))
                                 a3' (Z_to_bv 64 (oc row / 4)) a5' a6' a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    intros P ra' t0' t1' t2' a1' a3' a5' a6' a7' s2' s3' t3' t4' t5' t6' m' j L1 EP Hb Hsy HF HS HO.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro & Mi & Mo & Sum).
    pose proof (rs_oc_range row) as RO.
    assert (LP : length P = Z.to_nat (ic row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 1) (Z.to_nat (oc row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (oc row / 4)))).
    { rewrite (rs_slots_2 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (ic row / 4) + Z.to_nat (oc row / 4)))%nat by lia. reflexivity. }
    unfold at_, R0.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - eapply at_dd8; [rewrite LP; lia | | exact Hb | exact Hsy | exact HF | exact HS | exact HO].
      rewrite ES, O0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. step. rewrite rs_seqz by lia. step. step.
      replace (Z_to_bv 64 (oc row / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (oc row / 4)))) by (f_equal; lia).
      eapply (l2b (Z.to_nat (oc row / 4)) P); [lia | lia | symmetry; exact ES | exact Hb | exact Hsy | exact HF | exact HS
        | exact HO].
  Qed.

  (* lay = 1: the output slots (1), at 0x14ad0. *)
  Lemma l1a : forall k P n ra' t0' t1' t2' a7' s2' s3' t3' t4' t5' t6' m' j,
    lay row = 1 -> (length P + k = n)%nat -> n = Z.to_nat (oc row / 4) -> (0 < k)%nat -> P = repeat (bz 1) (length P) ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14ad0 (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (ic row))
                                 (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P))) (Z_to_bv 64 (ic row / 4))
                                 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat k))
                                 (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P))) a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros P n ra' t0' t1' t2' a7' s2' s3' t3' t4' t5' t6' m' j
      L1 Hn En Hk EP Hb Hsy HF HS HO; [lia|].
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro & Mi & Mo & Sum).
    unfold at_, R0.
    bstep. bstep.
    vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (Z.of_nat (S k) + -1) 0) by lia.
    rewrite mb_fill_step in HO by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HO.
    replace (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P) + 1))
      with (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length (P ++ [bz 1])))) by (f_equal; rewrite length_app; cbn [length]; lia).
    assert (EP' : P ++ [bz 1] = repeat (bz 1) (length (P ++ [bz 1])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (Z.of_nat 1 + -1 =? 0) with true by reflexivity. cbv iota.
      replace (Z_to_bv 64 (Z.of_nat n)) with (Z_to_bv 64 (Z.of_nat (length (P ++ [bz 1]))))
        by (f_equal; rewrite length_app; cbn [length]; lia).
      eapply (at_d34 (P ++ [bz 1])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia | exact Hb
        | exact Hsy | exact HF | exact HS | exact HO].
    - replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      eapply (IH (P ++ [bz 1]) n); [exact L1 | rewrite length_app; cbn [length]; lia | exact En | lia | exact EP' | exact Hb
        | exact Hsy | exact HF | exact HS | exact HO].
  Qed.

  (* lay <> 1: the input slots (2), at 0x14eec. *)
  Lemma l1b : forall k P n ra' t0' t1' t2' a7' s2' s3' t3' t4' t5' t6' m' j,
    lay row <> 1 -> (length P + k = n)%nat -> n = Z.to_nat (ic row / 4) -> (0 < k)%nat -> P = repeat (bz 2) (length P) ->
    bv_unsigned wb = 0 -> synok row = true ->
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (H8 ++ P ++ zeros (24 - length P))] ->
    evt rsegs Q (at_ 0x14eec (R0 ra' t0' t1' t2' wo wp (Z_to_bv 64 (Z.of_nat n))
                                 (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P))) (Z_to_bv 64 (oc row))
                                 (Z_to_bv 64 2) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (Z.of_nat k))
                                 (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P))) a7' s2' s3' t3' t4' t5' t6') m').
  Proof.
    induction k as [|k IH]; intros P n ra' t0' t1' t2' a7' s2' s3' t3' t4' t5' t6' m' j
      L1 Hn En Hk EP Hb Hsy HF HS HO; [lia|].
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro & Mi & Mo & Sum).
    unfold at_, R0.
    bstep. bstep.
    vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (Z.of_nat (S k) + -1) 0) by lia.
    rewrite mb_fill_step in HO by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 2))) with (bz 2) in HO.
    replace (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length P) + 1))
      with (Z_to_bv 64 (bv_unsigned wo + Z.of_nat (8 + length (P ++ [bz 2])))) by (f_equal; rewrite length_app; cbn [length]; lia).
    assert (EP' : P ++ [bz 2] = repeat (bz 2) (length (P ++ [bz 2])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (Z.of_nat 1 + -1 =? 0) with true by reflexivity. cbv iota.
      replace (Z_to_bv 64 (Z.of_nat n)) with (Z_to_bv 64 (Z.of_nat (length (P ++ [bz 2]))))
        by (f_equal; rewrite length_app; cbn [length]; lia).
      eapply (at_d88 (P ++ [bz 2])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia | exact Hb
        | exact Hsy | exact HF | exact HS | exact HO].
    - replace (Z.of_nat (S (S k)) + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      replace (Z_to_bv 64 (Z.of_nat (S (S k)) + -1)) with (Z_to_bv 64 (Z.of_nat (S k))) by (f_equal; lia).
      eapply (IH (P ++ [bz 2]) n); [exact L1 | rewrite length_app; cbn [length]; lia | exact En | lia | exact EP' | exact Hb
        | exact Hsy | exact HF | exact HS | exact HO].
  Qed.

  (* build_config refuses the row: the block stays zero, rc -1. *)
  Lemma ex0 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 0 -> synok row = false -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14eb0 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb Hn HF HS HO.
    eapply (epi (-1) (zeros 32)); [exact HF | exact HS | exact (mb_rw1 _ _ _ _ _ HO) | | ].
    - rewrite Hb, mb_synth0, Hn. reflexivity.
    - rewrite Hb, mb_rc0, Hn. reflexivity.
  Qed.

  Lemma case0 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 0 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14a04 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_rd4 rsegs m' (bv_unsigned wp) row 16 HR ltac:(lia)) as RD1. change (Z.of_nat 16) with 16 in RD1.
    pose proof (rs_rd4 rsegs m' (bv_unsigned wp) row 20 HR ltac:(lia)) as RD2. change (Z.of_nat 20) with 20 in RD2.
    pose proof (rs_ic_range row) as RI. pose proof (rs_oc_range row) as RO.
    unfold at_, R0. step. step.
    replace (Z.land (bv_unsigned wp) 7) with 0
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hp8; reflexivity).
    nf.
    step. rewrite rs_sx32_ic.
    step. rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (ic row) 0) as [C|Ci]; cbv iota.
    { eapply ex0; [exact Hb | apply mb_synok_false; lia | exact HF | exact HS | exact HO]. }
    step. rewrite rs_sx32_oc.
    step. rewrite rs_lts0 by lia.
    destruct (Z.ltb_spec (oc row) 0) as [C|Co]; cbv iota.
    { eapply ex0; [exact Hb | apply mb_synok_false; lia | exact HF | exact HS | exact HO]. }
    step. step. step. rewrite rs_or3 by lia.
    destruct (Z.eqb_spec (ic row mod 4) 0) as [Mi|Mi]; destruct (Z.eqb_spec (oc row mod 4) 0) as [Mo|Mo];
      cbn [andb negb]; cbv iota;
      try (eapply ex0; [exact Hb | apply mb_synok_false; lia | exact HF | exact HS | exact HO]).
    step. rewrite rs_srliw2 by lia. step. rewrite rs_srliw2 by lia.
    step. step. step. rewrite rc_ltu_lit by lia.
    destruct (Z.ltb_spec 12 (oc row / 4 + ic row / 4)) as [C|Cs]; cbv iota.
    { eapply ex0; [exact Hb | apply mb_synok_false; lia | exact HF | exact HS | exact HO]. }
    assert (Hsy : synok row = true) by (apply mb_synok_iff; lia).
    pose proof (proj2 HO) as WO. cbn [cells_size csize Nat.add] in WO.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) _ 0 1 WO ltac:(lia) ltac:(lia)) as HS0.
    rewrite Z.add_0_r, (wa_of_var wo (bv_unsigned wo) eq_refl) in HS0. clear WO RD1 RD2.
    destruct HS as (ST & MU & WM & MI). unfold FR in HF.
    step. step. step. st0. clear HS0. bstep.
    step. step. step. bstep.
    step. step. bstep.
    step. step. step. bstep.
    match goal with H : bytes_at rsegs ?mm (bv_unsigned wp) row |- _ =>
      pose proof (rd_byte rsegs mm _ row 252 H ltac:(lia)) as RDa end. change (Z.of_nat 252) with 252 in RDa.
    step. step. step. try (rewrite le1_zxb; mem_after_store_opt). bstep.
    step. step. bstep.
    step. step. bstep.
    match goal with H : bytes_at rsegs ?mm (bv_unsigned wp) row |- _ =>
      pose proof (rd_byte rsegs mm _ row 253 H ltac:(lia)) as RDb end. change (Z.of_nat 253) with 253 in RDb.
    step. step. try (rewrite le1_zxb; mem_after_store_opt).
    match goal with H : bytes_at rsegs ?mm (bv_unsigned wp) row |- _ =>
      pose proof (rd_byte rsegs mm _ row 290 H ltac:(lia)) as RDc end. change (Z.of_nat 290) with 290 in RDc.
    step. step. step.
    rewrite rs_zxb_eqb by lia. change (bv_unsigned (nth 290 row (Z_to_bv 8 0))) with (lay row).
    apply (rs_rw_take _ _ _ _ 9) in HO.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HO.
    match type of HO with rw_cells _ _ _ [CB 32 ?X0] =>
      replace X0 with (H8 ++ zeros 24) in HO by (unfold H8, sel, strap, zeros, bz; cbn [map repeat app skipn]; mb_bytes) end.
    destruct (Z.eqb_spec (lay row) 1) as [L1|L1]; cbn [negb]; cbv iota.
    - step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
      + step.
        eapply (at_d34 []); [exact L1 | rewrite O0; reflexivity | exact Hb | exact Hsy | exact HF
          | exact (conj ST (conj MU (conj WM MI))) | exact HO].
      + step. step. rewrite rs_seqz by lia. step. step. step. step.
        replace (Z_to_bv 64 (oc row / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (oc row / 4)))) by (f_equal; lia).
        eapply (l1a (Z.to_nat (oc row / 4)) [] (Z.to_nat (oc row / 4))); [exact L1 | reflexivity | reflexivity | lia
          | reflexivity | exact Hb | exact Hsy | exact HF | exact (conj ST (conj MU (conj WM MI))) | exact HO].
    - step. rewrite rc_eqb_lit by lia.
      destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
      + step.
        eapply (at_d88 []); [exact L1 | rewrite I0; reflexivity | exact Hb | exact Hsy | exact HF
          | exact (conj ST (conj MU (conj WM MI))) | exact HO].
      + step. step. step. rewrite rs_seqz by lia. step. step. step.
        replace (Z_to_bv 64 (ic row / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (ic row / 4)))) by (f_equal; lia).
        eapply (l1b (Z.to_nat (ic row / 4)) [] (Z.to_nat (ic row / 4))); [exact L1 | reflexivity | reflexivity | lia
          | reflexivity | exact Hb | exact Hsy | exact HF | exact (conj ST (conj MU (conj WM MI))) | exact HO].
  Qed.
  Lemma case3 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 3 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14b8c (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_rd2 rsegs m' (bv_unsigned wp) row 266 HR ltac:(lia)) as RD.
    change (Z.of_nat 266) with 266 in RD.
    pose proof (rs_rw16_range row 266) as Rv.
    unfold at_, R0. step. step.
    replace (Z.land (bv_unsigned wp) 7) with 0
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hp8; reflexivity).
    nf.
    step. try rewrite rs_zx16.
    step.
    rewrite (unsigned_lit (rw16 row 266)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
    step. step.
    destruct (Z.leb_spec (rw16 row 266) 9999) as [V|V].
    2:{ nf. step. step.
        eapply (epi (-1) (zeros 32)); [exact HF | exact HS | exact (mb_rw1 _ _ _ _ _ HO) | | ].
        - rewrite Hb, mb_synth3. unfold fwm.
          replace (rw16 row 266 <=? 9999) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
        - rewrite Hb, mb_rc3. unfold fwm.
          replace (rw16 row 266 <=? 9999) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    nt.
    destruct HS as (ST & MU & WM & MI). unfold FR in HF.
    do 8 step. bstep.
    do 14 step. bstep.
    do 14 step. bstep.
    do 9 step.
    pose proof (mb_mid _ _ _ [_] [_; _; _; _] _ HF) as HD.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in HD.
    apply (bytes_at_addr _ _ _ (bv_unsigned sp - 77)) in HD; [|lia].
    apply (rs_rw_take _ _ _ _ 6) in HF.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HF.
    match type of HD with bytes_at _ _ _ ?D =>
      eapply (call_bd D); [reflexivity | rewrite unsigned_lit by lia; lia | reflexivity | cbn [length]; lia
        | exact HF | exact (conj ST (conj MU (conj WM MI))) | exact HO | exact HD | |];
      [ rewrite Hb, mb_synth3; unfold fwm;
        replace (rw16 row 266 <=? 9999) with true by (symmetry; apply Z.leb_le; lia);
        unfold dt1s; change (bv_unsigned (Z_to_bv 64 0)) with 0;
        replace D with (digits (rw16 row 266)); [reflexivity|]
      | rewrite Hb, mb_rc3; unfold fwm;
        replace (rw16 row 266 <=? 9999) with true by (symmetry; apply Z.leb_le; lia); reflexivity ]
    end.
    unfold digits. cbn [map]. apply mb_l4; unfold bz; rs_brute_tac (rw16 row 266).
  Qed.
  Lemma case4 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 4 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14af0 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_rw16_range row 268) as R1. pose proof (rs_rw16_range row 270) as R2.
    pose proof (rs_rw16_range row 272) as R3.
    destruct HS as (ST & MU & WM & MI). unfold FR in HF.
    unfold at_, R0.
    step. step. step. bstep.
    step. step. step.
    replace (Z.land (bv_unsigned wp) 7) with 0
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hp8; reflexivity).
    nf.
    step. bstep.
    pose proof (rs_rd2 rsegs _ (bv_unsigned wp) row 268 HR ltac:(lia)) as RD1. change (Z.of_nat 268) with 268 in RD1.
    step. try rewrite rs_zx16.
    step. step. step. bstep.
    step. step. bstep.
    pose proof (rs_rd2 rsegs _ (bv_unsigned wp) row 270 HR ltac:(lia)) as RD2. change (Z.of_nat 270) with 270 in RD2.
    step. try rewrite rs_zx16.
    step. step. step. bstep.
    step. step. bstep.
    pose proof (rs_rd2 rsegs _ (bv_unsigned wp) row 272 HR ltac:(lia)) as RD3. change (Z.of_nat 272) with 272 in RD3.
    step. try rewrite rs_zx16.
    step. step. step. bstep.
    step.
    do 6 step.
    pose proof (mb_mid _ _ _ [_] [_; _; _; _; _; _; _; _] _ HF) as HD.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in HD.
    apply (bytes_at_addr _ _ _ (bv_unsigned sp - 77)) in HD; [|lia].
    apply (rs_rw_take _ _ _ _ 10) in HF.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HF.
    match type of HD with bytes_at _ _ _ ?D =>
      eapply (call_bd D); [reflexivity | rewrite unsigned_lit by lia; lia | reflexivity | cbn [length]; lia
        | exact HF | exact (conj ST (conj MU (conj WM MI))) | exact HO | exact HD | | rewrite Hb; reflexivity];
      rewrite Hb, mb_synth4; unfold dt1s; change (bv_unsigned (Z_to_bv 64 1536)) with 1536;
      replace D with (rvb row); [reflexivity|]
    end.
    unfold rvb.
    apply mb_cons; [reflexivity|]. apply mb_cons; [reflexivity|].
    apply mb_cons; [apply mb_whi; lia|]. apply mb_cons; [apply mb_wlo; lia|].
    apply mb_cons; [apply mb_whi; lia|]. apply mb_cons; [apply mb_wlo; lia|].
    apply mb_cons; [apply mb_whi; lia|]. apply mb_cons; [apply mb_wlo; lia|].
    reflexivity.
  Qed.
  Lemma case5 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 5 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14bc4 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_rd4 rsegs m' (bv_unsigned wp) row 56 HR ltac:(lia)) as RD.
    change (Z.of_nat 56) with 56 in RD.
    pose proof (rs_rw32_range row 56) as Rh.
    unfold at_, R0. step. step.
    replace (Z.land (bv_unsigned wp) 7) with 0
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hp8; reflexivity).
    nf.
    step. step.
    rewrite mb_sx32_eq0 by lia.
    destruct (Z.eqb_spec (rw32 row 56) 0) as [H0|H0]; cbv iota.
    { step. step.
      eapply (epi 0 (zeros 32)); [exact HF | exact HS | exact (mb_rw1 _ _ _ _ _ HO) | | ].
      - rewrite Hb, mb_synth5. unfold has. rewrite H0. reflexivity.
      - rewrite Hb, mb_rc5. unfold has. rewrite H0. reflexivity. }
    step. step. step.
    eapply (call_nf 3 0x14be0 (zeros 32)); [apply ret_pc_even; [lia | reflexivity] | lia | reflexivity
      | rewrite unsigned_lit by lia; lia | lia | exact H0 | exact HF | exact HS | exact HO |].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 HF2 HS2 HO2 HNM LN.
    unfold at_, R0. do 5 step. step.
    pose proof HS2 as (ST2 & MU2 & WM2 & MI2).
    pose proof HO2 as [_ WO2]. cbn [cells_size csize Nat.add] in WO2.
    pose proof HDH as HD0. unfold dt1_head_contract, DT1_HEAD in HD0.
    eapply evt_cut.
    { eapply HD0; [lia | apply (wr_at_prefix _ _ _ (Z.of_nat 32)); [exact WO2 | lia]]. }
    intros ms' PO. destruct PO as (c1 & c2 & c4 & c5 & m3 & E & HB3 & MU3 & WM3 & MI3). subst ms'.
    specialize (MI3 MI2).
    assert (HO3 : rw_cells rsegs m3 (bv_unsigned wo) [CB 32 (upd_bytes (zeros 32) 0 (dt1_bytes 1 22 4096))]).
    { eapply (mb_upd _ m2 m3 _ 32 _ 0 20 _ [(bv_unsigned wo, bv_unsigned wo + 20)]);
        [exact HO2 | lia | exact MU3 | exact WM3 | dj | dj | | reflexivity].
      change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact HB3. }
    destruct (mb_call _ m2 m3 _ HF2 HS2 MU3 WM3 MI3 ltac:(dj) ltac:(sfp)
                (stk_transport_disjoint rsegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(dj))) as [HF3 HS3].
    pose proof (bytes_at_transport rsegs _ m2 m3 _ _ HNM MU3 ltac:(dj)) as HNM3.
    replace (ret_pc (Z_to_bv 64 0x14bf8)) with (Z_to_bv 64 0x14bf8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    clear MU3 WM3 HO2 HB3 HNM.
    destruct HS3 as (ST3 & MUf & WMf & MIf). unfold FR in HF3.
    step. bstep. step. step. bstep.
    step. step. step. step.
    apply (rs_rw_take _ _ _ _ 3) in HO3.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HO3.
    eapply (call_mc 0x14c1c 21 10 (bv_unsigned sp - 77) (firstn 10 (nmr row nb)));
      [apply ret_pc_even; [lia | reflexivity] | lia | rewrite length_firstn, LN; reflexivity
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | lia
      | exact HF3 | exact (conj ST3 (conj MUf (conj WMf MIf))) | exact HO3 | |].
    { pose proof (bytes_at_sub _ _ _ _ 0 10 HNM3 ltac:(lia)) as H.
      apply (bytes_at_addr _ _ _ (bv_unsigned sp - 77)) in H; [exact H | lia]. }
    intros u0' u1' u2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' u3' u4' u5' u6' m4 HF4 HS4 _ _ HO4.
    unfold at_, R0. do 4 step.
    match type of HO4 with rw_cells _ _ _ [CB 32 (upd_bytes ?X' _ _)] =>
      assert (LX' : length X' = 32%nat) by reflexivity end.
    match type of HO4 with rw_cells _ _ _ [CB 32 ?X5] =>
      eapply (loop5 31 0 X5); [lia | lia | | | exact HF4 | exact HS4 | exact HO4 | |] end.
    - rewrite upd_bytes_length; [exact LX' | rewrite length_firstn, LN, LX'; lia].
    - rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. reflexivity.
    - rewrite Hb, mb_synth5. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idf. f_equal. rewrite mb_first_upd; [| exact LX' | rewrite length_firstn, LN; reflexivity].
      unfold idf31. f_equal.
      cbn [firstn skipn app upd_bytes zeros repeat dt1_bytes map length Nat.add Nat.sub].
      mb_bytes.
    - rewrite Hb, mb_rc5. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.
  Lemma case6 : forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j,
    bv_unsigned wb = 6 -> FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x14c48 (R0 ra' t0' t1' t2' wo wp a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (-1)) s3'
                                 t3' t4' t5' t6') m').
  Proof.
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' m' j Hb HF HS HO.
    pose proof (mb_row m' HS) as HR.
    pose proof (rs_rd4 rsegs m' (bv_unsigned wp) row 56 HR ltac:(lia)) as RD.
    change (Z.of_nat 56) with 56 in RD.
    pose proof (rs_rw32_range row 56) as Rh.
    unfold at_, R0. step. step.
    replace (Z.land (bv_unsigned wp) 7) with 0
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hp8; reflexivity).
    nf.
    step. step.
    rewrite mb_sx32_eq0 by lia.
    destruct (Z.eqb_spec (rw32 row 56) 0) as [H0|H0]; cbv iota.
    { step. step.
      eapply (epi 0 (zeros 32)); [exact HF | exact HS | exact (mb_rw1 _ _ _ _ _ HO) | | ].
      - rewrite Hb, mb_synth6. unfold has. rewrite H0. reflexivity.
      - rewrite Hb, mb_rc6. unfold has. rewrite H0. reflexivity. }
    step. step. step.
    eapply (call_nf 24 0x14c64 (zeros 32)); [apply ret_pc_even; [lia | reflexivity] | lia | reflexivity
      | rewrite unsigned_lit by lia; lia | lia | exact H0 | exact HF | exact HS | exact HO |].
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 HF2 HS2 HO2 HNM LN.
    destruct HS2 as (ST2 & MU2 & WM2 & MI2). unfold FR in HF2. unfold at_, R0.
    step. step. step. step. bstep.
    step. step. bstep.
    step. step. step. bstep.
    step. step. bstep.
    step. step. step. step. bstep.
    step. step. step. step.
    pose proof (mb_mid _ _ _ [_] [_; _; _; _; _] _ HF2) as HR5.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in HR5.
    apply (bytes_at_addr _ _ _ (bv_unsigned sp - 77)) in HR5; [|lia].
    apply (rs_rw_take _ _ _ _ 7) in HF2.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HF2.
    eapply (call_mcf 0x14cc4 8 16 (bv_unsigned sp - 56) (nmr row nb));
      [apply ret_pc_even; [lia | reflexivity] | lia | exact LN
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | lia
      | exact HF2 | exact (conj ST2 (conj MU2 (conj WM2 MI2))) | exact HO2
      | apply (bytes_at_addr _ _ _ _ _ HNM); lia | ].
    intros u0' u1' u2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' u3' u4' u5' u6' m3 HF3 HS3 HO3 MU3 HNM8.
    pose proof (bytes_at_transport rsegs _ _ m3 _ _ HR5 MU3 ltac:(cbn [length]; dj)) as HR5'.
    pose proof (bytes_at_transport rsegs _ _ m3 _ _ HNM MU3 ltac:(rewrite LN; dj)) as HNM'.
    pose proof (bytes_at_cat _ _ _ _ _ _ HR5' HNM8 ltac:(cbn [length]; lia)) as HREC.
    clear MU3 HR5 HNM HR5'.
    match type of HREC with bytes_at _ _ _ ?R => assert (LREC : length R = 21%nat) by (rewrite length_app, LN; reflexivity) end.
    destruct HS3 as (ST3 & MUf & WMf & MIf). unfold FR in HF3. unfold at_, R0.
    pose proof (proj2 HO3) as WO3. cbn [cells_size csize Nat.add] in WO3.
    pose proof (wr_at_store_ok rsegs m3 (bv_unsigned wo) _ 0 1 WO3 ltac:(lia) ltac:(lia)) as HS0.
    rewrite Z.add_0_r, (wa_of_var wo (bv_unsigned wo) eq_refl) in HS0. clear WO3.
    step. step. step. st0. clear HS0. bstep.
    step. step. step. bstep.
    step. step. bstep.
    step. step. step. bstep.
    step. step. bstep.
    step. step. step. bstep.
    step. step. bstep.
    step. step. step. bstep.
    step. step. step. bstep.
    step. step. step.
    rewrite mb_sltiu1 by lia. step. nfc.
    apply (rs_rw_take _ _ _ _ 10) in HO3.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HO3.
    step. step. step. step.
    eapply (call_mc 0x14d68 9 6 (bv_unsigned sp - 46) (firstn 6 (skipn 10 (nmr row nb))));
      [apply ret_pc_even; [lia | reflexivity] | lia | rewrite length_firstn, length_skipn, LN; reflexivity
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | reflexivity | lia
      | exact HF3 | exact (conj ST3 (conj MUf (conj WMf MIf))) | exact HO3 | |].
    { pose proof (bytes_at_sub _ _ _ _ 10 6 HNM' ltac:(lia)) as H.
      apply (bytes_at_addr _ _ _ (bv_unsigned sp - 46)) in H; [exact H | lia]. }
    intros u0'' u1'' u2'' a1''' a2''' a3''' a4''' a5''' a6''' a7''' u3'' u4'' u5'' u6'' m4 HF4 HS4 MU4 _ HO4.
    pose proof (bytes_at_transport rsegs _ _ m4 _ _ HREC MU4 ltac:(dj)) as HREC4.
    unfold at_, R0. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned sp + -77)) with (Z_to_bv 64 (bv_unsigned sp - 77 + Z.of_nat 0))
      by (f_equal; lia).
    match type of HO4 with rw_cells _ _ _ [CB 32 (upd_bytes ?X0 9 ?S0)] =>
      replace X0 with (map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ zeros 23) in HO4
        by (unfold zeros, bz; cbn [map repeat app skipn]; mb_bytes) end.
    match type of HO4 with rw_cells _ _ _ [CB 32 ?X6] => match type of HREC4 with bytes_at _ _ _ ?R =>
      eapply (loopr 21 0 R X6); [lia | lia | exact LREC | | exact HREC4 | exact HF4 | exact HS4 | exact HO4 | |]
    end end.
    - rewrite upd_bytes_length by (rewrite length_firstn, length_skipn, LN; simpl; lia). simpl. reflexivity.
    - rewrite Hb, mb_synth6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idl. f_equal.
      rewrite mb_idl_eq by first [reflexivity | rewrite length_firstn, length_skipn, LN; reflexivity].
      match type of HREC4 with bytes_at _ _ _ (?A ++ ?B) =>
        assert (EPS : psum (A ++ B) 21 = 22 + psum B 16)
          by (change (psum (A ++ B) 21) with (psum (A ++ B) (length A + 16)); rewrite mb_psum_app;
              f_equal; vm_compute; reflexivity) end.
      rewrite EPS. unfold idl31, idlc. reflexivity.
    - rewrite Hb, mb_rc6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.

  Lemma disp : forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j,
    FR m' j -> FS m' -> rw_cells rsegs m' (bv_unsigned wo) [CB 32 (zeros 32)] ->
    evt rsegs Q (at_ 0x149e0 (R0 (Z_to_bv 64 0x149e0) t0' t1' t2' wo wp wo a1' a2' a3' a4' a5' a6' a7'
                                  (Z_to_bv 64 (-1)) wb t3' t4' t5' t6') m').
  Proof.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j HF HS HO.
    pose proof (zr_word wb) as Rb. unfold inr64 in Rb.
    pose proof HS as (_ & _ & _ & MI).
    unfold at_, R0. step. step.
    destruct (Z.ltb_spec 6 (bv_unsigned wb)) as [B6|B6].
    - nt. eapply (epi (-1) (zeros 32)); [exact HF | exact HS | exact (mb_rw1 _ _ _ _ _ HO) | | ].
      + unfold synth. replace (6 <? bv_unsigned wb) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      + unfold rc. replace (6 <? bv_unsigned wb) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - nf.
      assert (Bk : bv_unsigned wb = 0 \/ bv_unsigned wb = 1 \/ bv_unsigned wb = 2 \/ bv_unsigned wb = 3 \/
                   bv_unsigned wb = 4 \/ bv_unsigned wb = 5 \/ bv_unsigned wb = 6) by lia.
      destruct Bk as [Bk|[Bk|[Bk|[Bk|[Bk|[Bk|Bk]]]]]]; rewrite (mb_word wb _ Bk);
        step; step; step; step; step; step; step;
        [ eapply case0 | eapply case1 | eapply case2 | eapply case3 | eapply case4 | eapply case5 | eapply case6 ];
        first [exact Bk | exact HF | exact HS | exact HO].
  Qed.

  Lemma run : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 wp wb wo a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    pose proof disp as DISP.
    pose proof ST0 as ST. pose proof HOC0 as HO. pose proof MI0 as MI.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned wo, bv_unsigned wo + 32)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold REAC_BOX_MODEL_BLOCK.
    step.
    carve_frame 80%nat ST.
    step. step. step. step. step. step. step.
    nf. step. step. nf.
    step. step. step. step. step. step.
    eapply evt_cut.
    { eapply HMS; [ | exact MI]. change (Z.to_nat (bv_unsigned (Z_to_bv 64 32))) with 32%nat. exact HO. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & MU2 & WM2 & MI2 & RW2).
    subst ms'.
    change (Z.to_nat (bv_unsigned (Z_to_bv 64 32))) with 32%nat in RW2.
    change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) 32) with (zeros 32) in RW2.
    change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU2.
    replace (ret_pc (Z_to_bv 64 0x149e0)) with (Z_to_bv 64 0x149e0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    match goal with FRc : rw_cells rsegs ?mc (bv_unsigned sp + -80) [CB 40 ?jj; _; _; _; _; _] |- _ =>
      assert (HF : FR mc jj) by exact FRc;
      assert (HS : FS mc) by (split; [exact ST | split; [exact MU | split; [exact WM | exact MI]]]) end.
    destruct (mb_call _ _ m2 _ HF HS MU2 WM2 MI2 ltac:(dj) ltac:(sfp)
                (stk_transport_disjoint rsegs _ _ m2 _ _ ST MU2 WM2 ltac:(dj))) as [HF2 HS2].
    eapply DISP; [exact HF2 | exact HS2 | exact RW2].
  Qed.
End Main.

Theorem reac_box_model_block_holds : memset_contract -> memcpy_contract -> dt1_head_contract -> name_field_contract ->
  build_dt1_single_contract -> reac_box_model_block_contract.
Proof.
  intros HMS HMC HDH HNF HBD. unfold reac_box_model_block_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p b o
    row nb ob E0 E1 E2 Rp Rb Ro Hal ST HP HN HO MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Rlo & _ & _).
  assert (U0 : bv_unsigned a0 = p) by (subst a0; apply unsigned_lit; lia).
  assert (U1 : bv_unsigned a1 = b) by (subst a1; apply unsigned_lit; lia).
  assert (U2 : bv_unsigned a2 = o) by (subst a2; apply unsigned_lit; lia).
  clear E0 E1 E2. subst p b o.
  destruct (Z.eq_dec (bv_unsigned a0) 0) as [P0|P0]; [apply mb_early; [exact ST | exact MI | left; exact P0]|].
  destruct (Z.eq_dec (bv_unsigned a2) 0) as [O0|O0]; [apply mb_early; [exact ST | exact MI | right; exact O0]|].
  destruct (HP P0) as (Hp8 & Hlen & HRB & DRS & DRO).
  destruct (HO O0) as (HOC & DOS & DOJ).
  pose proof (bytes_at_bound _ _ _ _ HRB) as BR. rewrite Hlen in BR.
  pose proof (rw_cells_bound rsegs m _ _ HOC) as BO. cbn [cells_size csize Nat.add] in BO.
  eapply run; try eassumption; try lia.
  intros B56 H1 H2. destruct (HN P0 B56 H1 H2) as (OK & NB & D1 & D2).
  split; [exact OK|]. split; [exact NB|]. split; [exact D1|]. lia.
Qed.
