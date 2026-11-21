(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition Z_DIST_CODE : Z := 0x11b10.        (* [comment removed for export] *)
Definition Z_LENGTH_CODE : Z := 0x11d10.      (* [comment removed for export] *)
Definition Z_STATIC_LTREE : Z := 0x11e10.     (* [comment removed for export] *)
Definition Z_STATIC_DTREE : Z := 0x12290.     (* [comment removed for export] *)
Definition Z_EXTRA_LBITS : Z := 0x12308.      (* [comment removed for export] *)
Definition Z_EXTRA_DBITS : Z := 0x1237c.      (* [comment removed for export] *)
Definition Z_BL_ORDER : Z := 0x12440.         (* [comment removed for export] *)
Definition Z_BASE_LENGTH : Z := 0x12454.      (* [comment removed for export] *)
Definition Z_BASE_DIST : Z := 0x124c8.        (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u16ro_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u16s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 2 * i) ->
  ov_read_bytes psegs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i) with (Z.of_nat (2 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u32ro_read : forall m A ws (i : Z) w a,
  bytes_at psegs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes psegs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read psegs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac rod_tac := intros m MI; apply ro_bytes_at; [exact MI| unfold Z_DIST_CODE, Z_LENGTH_CODE, Z_STATIC_LTREE, Z_STATIC_DTREE, Z_EXTRA_LBITS, Z_EXTRA_DBITS, Z_BL_ORDER, Z_BASE_LENGTH, Z_BASE_DIST; lia
  | vm_compute; intros; discriminate | apply ro_bytes_b_sound; vm_compute; reflexivity].

Lemma rod_dist_code : forall m, mem_inv psegs m -> bytes_at psegs m Z_DIST_CODE (av8 dist_code_a 512).
Proof. rod_tac. Qed.
Lemma rod_length_code : forall m, mem_inv psegs m -> bytes_at psegs m Z_LENGTH_CODE (av8 length_code_a 256).
Proof. rod_tac. Qed.
Lemma rod_bl_order : forall m, mem_inv psegs m -> bytes_at psegs m Z_BL_ORDER (av8 bl_order_a 19).
Proof. rod_tac. Qed.
Lemma rod_static_ltree : forall m, mem_inv psegs m -> bytes_at psegs m Z_STATIC_LTREE (u16s (avct static_ltree_fc static_ltree_dl 288)).
Proof. rod_tac. Qed.
Lemma rod_static_dtree : forall m, mem_inv psegs m -> bytes_at psegs m Z_STATIC_DTREE (u16s (avct static_dtree_fc static_dtree_dl 30)).
Proof. rod_tac. Qed.
Lemma rod_extra_lbits : forall m, mem_inv psegs m -> bytes_at psegs m Z_EXTRA_LBITS (u32s (av32 extra_lbits_a 29)).
Proof. rod_tac. Qed.
Lemma rod_extra_dbits : forall m, mem_inv psegs m -> bytes_at psegs m Z_EXTRA_DBITS (u32s (av32 extra_dbits_a 30)).
Proof. rod_tac. Qed.
Lemma rod_base_length : forall m, mem_inv psegs m -> bytes_at psegs m Z_BASE_LENGTH (u32s (av32 base_length_a 29)).
Proof. rod_tac. Qed.
Lemma rod_base_dist : forall m, mem_inv psegs m -> bytes_at psegs m Z_BASE_DIST (u32s (av32 base_dist_a 30)).
Proof. rod_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zforall_lt : forall (P : Z -> bool) n, forallb P (zseq n) = true -> forall i, 0 <= i < n -> P i = true.
Proof.
  intros P n H i Hi. rewrite forallb_forall in H. apply H. eapply nth_error_In. apply (zseq_nth n i Hi).
Qed.

Ltac ztab_tac n P H :=
  let X := fresh "X" in
  pose proof (zforall_lt P n ltac:(vm_compute; reflexivity) _ H) as X; cbv beta in X;
  repeat (apply andb_true_iff in X; let Y := fresh "Y" in destruct X as [X Y]);
  repeat match goal with
  | Y : (_ <=? _) = true |- _ => apply Z.leb_le in Y
  | Y : (_ <? _) = true |- _ => apply Z.ltb_lt in Y
  | Y : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in Y
  end.

Lemma length_code_range : forall lc, 0 <= lc < 256 -> 0 <= arr_get length_code_a lc < 29.
Proof. intros lc H. ztab_tac 256 (fun i => (0 <=? arr_get length_code_a i) && (arr_get length_code_a i <? 29)) H. lia. Qed.

Lemma dist_code_range : forall i, 0 <= i < 512 -> 0 <= arr_get dist_code_a i < 30.
Proof. intros i H. ztab_tac 512 (fun i => (0 <=? arr_get dist_code_a i) && (arr_get dist_code_a i <? 30)) H. lia. Qed.

(* [comment removed for export] *)
Lemma extra_lbits_facts : forall c, 0 <= c < 29 ->
  0 <= arr_get extra_lbits_a c <= 5 /\ 0 <= arr_get base_length_a c <= 255
  /\ (negb (arr_get extra_lbits_a c =? 0) = ((8 <=? c) && (c <=? 27))).
Proof.
  intros c H.
  ztab_tac 29 (fun c => (0 <=? arr_get extra_lbits_a c) && (arr_get extra_lbits_a c <=? 5) && (0 <=? arr_get base_length_a c) && (arr_get base_length_a c <=? 255)
                        && Bool.eqb (negb (arr_get extra_lbits_a c =? 0)) ((8 <=? c) && (c <=? 27))) H.
  split; [lia|]. split; [lia|]. assumption.
Qed.

(* [comment removed for export] *)
Lemma extra_dbits_facts : forall c, 0 <= c < 30 ->
  0 <= arr_get extra_dbits_a c <= 13 /\ 0 <= arr_get base_dist_a c <= 24576
  /\ (negb (arr_get extra_dbits_a c =? 0) = (4 <=? c)).
Proof.
  intros c H.
  ztab_tac 30 (fun c => (0 <=? arr_get extra_dbits_a c) && (arr_get extra_dbits_a c <=? 13) && (0 <=? arr_get base_dist_a c) && (arr_get base_dist_a c <=? 24576)
                        && Bool.eqb (negb (arr_get extra_dbits_a c =? 0)) (4 <=? c)) H.
  split; [lia|]. split; [lia|]. assumption.
Qed.

Lemma length_base_le : forall lc, 0 <= lc < 256 -> arr_get base_length_a (arr_get length_code_a lc) <= lc.
Proof. intros lc H. ztab_tac 256 (fun i => arr_get base_length_a (arr_get length_code_a i) <=? i) H. lia. Qed.

Lemma dist_base_le : forall d, 0 <= d < 32768 -> 0 <= d_code d < 30 /\ arr_get base_dist_a (d_code d) <= d.
Proof.
  intros d H. unfold d_code. destruct (Z.ltb_spec d 256) as [C|C].
  - assert (H1 : 0 <= d < 256) by lia.
    ztab_tac 256 (fun i => (0 <=? arr_get dist_code_a i) && (arr_get dist_code_a i <? 30) && (arr_get base_dist_a (arr_get dist_code_a i) <=? i)) H1. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128.
    assert (H1 : 0 <= d / 128 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.mul_div_le d 128 ltac:(lia)) as LE.
    ztab_tac 256 (fun i => (0 <=? arr_get dist_code_a (256 + i)) && (arr_get dist_code_a (256 + i) <? 30) && (arr_get base_dist_a (arr_get dist_code_a (256 + i)) <=? 128 * i)) H1. lia.
Qed.
