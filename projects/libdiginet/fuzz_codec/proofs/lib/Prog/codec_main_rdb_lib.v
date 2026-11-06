From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv.
Import ListNotations.
Open Scope Z_scope.

(** The frame at a reader cut (k as HEAD leaves it), with the cursor cells in.p / in.n given as words. *)
Definition rd_cells (kind pv dv : Z) (inp inn : word) (tl : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0x13f0)] ++ kcall_cells (k_rd kind pv dv) ++ [C8 inp; C8 inn; CB 80 tl].

(** ---- 32-bit values ---- *)

Lemma swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_range : forall z, - 2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
  intros z. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). pose proof (Z.mod_pos_bound (z + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.

(** lw of a 32-bit cell is the C int of its unsigned value. *)
Lemma swrap32_s32 : forall z, bv_swrap 32 z = s32 (z mod 2 ^ 32).
Proof.
  intros z. unfold bv_swrap, bv_wrap, s32. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound z (2 ^ 32) ltac:(lia)) as Hr.
  rewrite <- Zplus_mod_idemp_l.
  remember (z mod 2 ^ 32) as r eqn:Er. clear Er.
  destruct (Z.ltb_spec r (2 ^ 31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_s32 : forall w : word, sx32 w = Z_to_bv 64 (s32 (bv_unsigned w mod 2 ^ 32)).
Proof. intros w. unfold sx32. rewrite swrap32_s32. reflexivity. Qed.

Lemma unsigned_mod32 : forall z, bv_unsigned (Z_to_bv 64 z) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(** ---- frame cells ---- *)

(** A cell replaced by another with the same bytes. *)
Lemma rw_cells_conv : forall m A cs k c c',
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> cbytes c' = cbytes c -> csize c' = csize c -> cell_wf c' ->
  rw_cells rsegs m A (cell_upd cs k c').
Proof.
  intros m A cs k c c' [[Hwf Hb] Hw] Hat Hby Hsz Hcw.
  destruct (cell_at_split cs k c c' Hat) as (pre & post & E & Hk & Eu).
  rewrite Eu. subst cs.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. cbn [cells_wf] in W2. destruct W2 as [_ W3].
  split; [split|].
  - apply cells_wf_app. split; [exact W1 | cbn [cells_wf]; split; assumption].
  - rewrite cells_bytes_app in *. cbn [cells_bytes] in *. rewrite Hby. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. exact Hw.
Qed.

Lemma cbytes_C4 : forall w w', bv_unsigned w mod 2 ^ 32 = bv_unsigned w' mod 2 ^ 32 -> cbytes (C4 w) = cbytes (C4 w').
Proof.
  intros w w' H. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned w') 32) by (cbn; lia).
  rewrite H. reflexivity.
Qed.

(** The 32-bit cell of word w holds the C int (or unsigned) v when their low 32 bits agree. *)
Lemma rw_cells_C4 : forall m A cs k w v,
  rw_cells rsegs m A cs -> cell_at cs k = Some (C4 w) -> v mod 2 ^ 32 = bv_unsigned w mod 2 ^ 32 ->
  rw_cells rsegs m A (cell_upd cs k (C4 (Z_to_bv 64 v))).
Proof.
  intros m A cs k w v H Hat Hv. eapply rw_cells_conv; [exact H | exact Hat | | reflexivity | exact I].
  apply cbytes_C4. rewrite unsigned_mod32. exact Hv.
Qed.

Lemma split_nth : forall {X} (cs : list X) i c, nth_error cs i = Some c -> cs = firstn i cs ++ c :: skipn (S i) cs.
Proof.
  intros X cs. induction cs as [|x cs IH]; intros [|i] c H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - f_equal. apply IH. exact H.
Qed.

(** The frame cut around its i-th cell. *)
Lemma rw_cells_cut3 : forall m A cs i c,
  rw_cells rsegs m A cs -> nth_error cs i = Some c ->
  rw_cells rsegs m A (firstn i cs) /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs))) [c] /\
  rw_cells rsegs m (A + Z.of_nat (cells_size (firstn i cs)) + Z.of_nat (csize c)) (skipn (S i) cs).
Proof.
  intros m A cs i c H Hn. rewrite (split_nth cs i c Hn) in H.
  apply rw_cells_app_split in H. destruct H as [H1 H23].
  change (c :: skipn (S i) cs) with ([c] ++ skipn (S i) cs) in H23.
  apply rw_cells_app_split in H23. destruct H23 as [H2 H3].
  cbn [cells_size] in H3. rewrite Nat.add_0_r in H3.
  split; [exact H1|]. split; [exact H2|]. exact H3.
Qed.

Lemma rw_cells_join3 : forall m A B C cs1 c cs3,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B [c] -> rw_cells rsegs m C cs3 ->
  B = A + Z.of_nat (cells_size cs1) -> C = B + Z.of_nat (csize c) ->
  rw_cells rsegs m A (cs1 ++ c :: cs3).
Proof.
  intros m A B C cs1 c cs3 H1 H2 H3 EB EC. subst B C.
  apply rw_cells_app_join; [exact H1|].
  change (c :: cs3) with ([c] ++ cs3). apply rw_cells_app_join; [exact H2|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H3.
Qed.

(** ---- the call record ---- *)

Lemma zb_fz0_24 : zb (fz0 24) = repeat 0 24.
Proof. vm_compute. reflexivity. Qed.

(** The reader widths of a record whose bytes are HEAD's zeros and n = 0. *)
Lemma rdr_fz0 : forall kind a b c d,
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= d < 2 ^ 31 ->
  (kind = 5 -> b < 2 ^ 16) -> (kind = 10 -> b < 256) -> (kind = 11 -> a < 256 /\ b < 256) ->
  reader_ok kind a b c d (zb (fz0 24)) 0.
Proof.
  intros kind a b c d Ha Hb Hc Hd H5 H10 H11. unfold reader_ok. rewrite zb_fz0_24.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply repeat_length|].
  split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
  split; [lia|]. split; [exact H5|]. split; [exact H10|]. exact H11.
Qed.

(** ---- tactics ---- *)

(** The input byte at cursor word cur (bv_unsigned cur = p + c) plus j, in the current memory. *)
Ltac in_byte cur c j :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with
    | HD : bytes_at rsegs m (bv_unsigned (e_p ?e)) (e_data ?e), HCUR : bv_unsigned cur = _ |- _ =>
      let HB := fresh "HB" in
      assert (HB : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned cur + j)) 1
                   = Some [nth (Z.to_nat (c + j)) (e_data e) (Z_to_bv 8 0)])
        by (rewrite HCUR; replace (bv_unsigned (e_p e) + c + j) with (bv_unsigned (e_p e) + (c + j)) by lia;
            apply (bytes_at_byte m (bv_unsigned (e_p e)) (e_data e) (c + j)); [exact HD | lia]);
      let Rb := fresh "Rb" in
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (c + j)) (e_data e) (Z_to_bv 8 0))) as Rb;
      unfold bv_modulus in Rb
    end
  end.

(** The same at offset 0, where the load address is the cursor word itself. *)
Ltac in_byte0 cur c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    lazymatch goal with
    | HD : bytes_at rsegs m (bv_unsigned (e_p ?e)) (e_data ?e), HCUR : bv_unsigned cur = _ |- _ =>
      let HB := fresh "HB" in
      assert (HB : ov_read_bytes rsegs m cur 1 = Some [nth (Z.to_nat c) (e_data e) (Z_to_bv 8 0)])
        by (rewrite <- (Z_to_bv_bv_unsigned cur); rewrite HCUR;
            apply (bytes_at_byte m (bv_unsigned (e_p e)) (e_data e) c); [exact HD | lia]);
      let Rb := fresh "Rb" in
      pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat c) (e_data e) (Z_to_bv 8 0))) as Rb;
      unfold bv_modulus in Rb
    end
  end.

(** Normalize the sizes and addresses in the pieces of rw_cells_cut3. *)
Ltac norm_piece H :=
  cbn [firstn skipn cells_size csize Nat.add] in H;
  repeat match type of H with
  | context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in is_Zlit v; change (Z.of_nat n) with v in H
  end.

(** The same in the goal. *)
Ltac norm_sizes :=
  cbn [cells_size csize Nat.add];
  repeat match goal with
  | |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in is_Zlit v; change (Z.of_nat n) with v
  end.
