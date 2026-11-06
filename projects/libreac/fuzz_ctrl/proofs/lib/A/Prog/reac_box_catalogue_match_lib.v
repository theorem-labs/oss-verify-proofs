(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c reac_box_catalogue_match_c.
Import ListNotations.
Open Scope Z_scope.

(* Reusable helpers for the asan proof of reac_box_catalogue_match (lib/A/Prog/reac_box_catalogue_match.v):
   the catalogue bytes at CM_T (0x9e800) and their rows, and the generic shadow/addressable idioms
   (as in lib/A/Prog/reac_ctrl_classify_box_frame.v). *)

(* The patched BOX_CATALOGUE of the asan image: 11 rows of 296 bytes. *)
Definition CM_TBL : list byte := match image_bytes rsegs CM_T 3256 with Some l => l | None => [] end.

Lemma CM_TBL_eq : image_bytes rsegs CM_T 3256 = Some CM_TBL.
Proof. vm_compute. reflexivity. Qed.

Lemma CM_TBL_len : length CM_TBL = 3256%nat.
Proof. exact (image_bytes_length rsegs 3256 CM_T CM_TBL CM_TBL_eq). Qed.

Definition cm_row (i : nat) : list byte := firstn 296 (skipn (296 * i) CM_TBL).

Lemma cm_row_ok : forall i, (i < 11)%nat -> synok (cm_row i) = true /\ gram (cm_row i) = nth i DECLS [].
Proof.
  intros i Hi.
  assert (E : forall j, (j < 11)%nat -> synok (cm_row j) && bool_decide (gram (cm_row j) = nth j DECLS []) = true).
  { intros j Hj. do 11 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
  pose proof (E i Hi) as Ei. apply andb_true_iff in Ei as [E1 E2].
  split; [exact E1|]. exact (bool_decide_eq_true_1 _ E2).
Qed.

Lemma cm_rc : forall i nb, (i < 11)%nat -> rc (cm_row i) 0 = 1 /\ synth (cm_row i) 0 nb = nth i DECLS [].
Proof.
  intros i nb Hi. destruct (cm_row_ok i Hi) as [A B]. unfold rc, synth. rewrite A.
  split; [reflexivity|]. rewrite <- B. reflexivity.
Qed.

Lemma cm_decl_len : forall i, (i < 11)%nat -> length (nth i DECLS []) = 32%nat.
Proof. intros i Hi. do 11 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma cm_row_len : forall i, (i < 11)%nat -> length (cm_row i) = 296%nat.
Proof. intros i Hi. unfold cm_row. rewrite length_firstn, length_skipn, CM_TBL_len. lia. Qed.

Lemma mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (byte_range a). pose proof (byte_range b).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma cm_eqb0 : forall v, -2^64 < v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|]. apply Z.eqb_neq. intros E'.
  apply E. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

(* ---- generic shadow / addressable idioms (as in reac_ctrl_classify_box_frame.v) ---- *)

Lemma acl_app_in : forall m p n i, addressable m p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros m p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma acl_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma acl_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma acl_addr_join : forall m p n n', addressable m p n -> addressable m (p + n) n' -> 0 <= n' ->
  addressable m p (n + n').
Proof.
  intros m p n n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply HA'. lia.
Qed.

Lemma acl_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma acl_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma acl_shadow : forall mc p n j w X, addressable mc p n -> 0 <= j -> 1 <= w -> j + w <= n ->
  X mod 8 + w <= 8 -> X = p + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc p n j w X HA Hj Hw Hjw Hm ->.
  pose proof (rt_shadow_rd mc p n [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc p n HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K p n [] j HSR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  exact (asan_check_lt rsegs mc ASAN_K p n j w k HAD Hj Hw Hjw Hm BK).
Qed.

Lemma acl_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma acl_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma acl_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma acl_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma acl_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (acl_sh_lt x lo Hm L). lia.
  - pose proof (acl_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma acl_S_mod8 : forall S j, S mod 16 = 0 -> j mod 8 = 0 -> (S - j) mod 8 = 0.
Proof. intros S j H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.

Lemma acl_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

(* The tls premise at a callee's return (fl_fp_ret for the thread cells). *)
Lemma acl_tls_ret : forall cs m m' TP FS lo hi W D Y Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y).
Proof.
  intros cs m m' TP FS lo hi W D Y Wm (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Htls Hm Hs DT TS C T DB k HT.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls _ _ _ _ _ _ HT0).
Qed.
