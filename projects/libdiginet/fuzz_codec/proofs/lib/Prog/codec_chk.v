From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

(** Two 64-bit literals of signed values in range are equal iff the values are. *)
Lemma chk_s64_eqb : forall v c, -2^63 <= v < 2^63 -> -2^63 <= c < 2^63 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
  intros v c Hv Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v c) as [->|Hne]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intro E. apply Hne.
  change (2^64) with 18446744073709551616 in E.
  change (2^63) with 9223372036854775808 in Hv, Hc.
  Z.div_mod_to_equations. lia.
Qed.

(** lw of an unsigned 32-bit value s: sx32 of it. *)
Lemma chk_sx32_unsigned : forall s, 0 <= s < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 s)) = if Z.ltb s (2^31) then s else s + (2^64 - 2^32).
Proof.
  intros s Hs. unfold sx32.
  rewrite (unsigned_lit s) by lia.
  rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  destruct (Z.ltb_spec s (2^31)).
  - rewrite (Z.mod_small (s + 2^31) (2^32)) by lia.
    replace (s + 2^31 - 2^31) with s by lia. apply Z.mod_small. lia.
  - replace (s + 2^31) with ((s - 2^31) + 1 * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (s - 2^31) (2^32)) by lia.
    replace (s - 2^31 - 2^31) with ((s + (2^64 - 2^32)) + (-1) * 2^64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma chk_sx32_eqb : forall s c, 0 <= s < 2^32 -> 0 <= c < 2^31 ->
  bv_eqb (sx32 (Z_to_bv 64 s)) (Z_to_bv 64 c) = Z.eqb s c.
Proof.
  intros s c Hs Hc. unfold bv_eqb. rewrite chk_sx32_unsigned by lia. rewrite (unsigned_lit c) by lia.
  destruct (Z.ltb_spec s (2^31)); [reflexivity|].
  destruct (Z.eqb_spec (s + (2^64 - 2^32)) c); destruct (Z.eqb_spec s c); first [reflexivity | exfalso; lia].
Qed.

(** Two sign-extended u32 loads are equal iff the u32 values are. *)
Lemma chk_sx32_eqb2 : forall s c, 0 <= s < 2^32 -> 0 <= c < 2^32 ->
  bv_eqb (sx32 (Z_to_bv 64 s)) (sx32 (Z_to_bv 64 c)) = Z.eqb s c.
Proof.
  intros s c Hs Hc. unfold bv_eqb. rewrite !chk_sx32_unsigned by lia.
  destruct (Z.ltb_spec s (2^31)); destruct (Z.ltb_spec c (2^31));
  destruct (Z.eqb_spec s c); first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Qed.

(** The 8-alignment test [andi a, x, 7]. *)
Lemma chk_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(** The bytes of a CB cell of a cell list lie at its offset. *)
Lemma chk_cells_at_cb : forall segs m A cs k n bs,
  cells_at segs m A cs -> cell_at cs k = Some (CB n bs) -> bytes_at segs m (A + Z.of_nat k) bs.
Proof.
  intros segs m A cs k n bs [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ (CB n bs) Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

(** memcmp over n bytes of two lists with the same first n bytes returns 0. *)
Lemma chk_memcmp_eq : forall n (l r : list byte), (n <= length l)%nat -> (n <= length r)%nat ->
  firstn n l = firstn n r -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros l r Hl Hr He; [reflexivity|].
  destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
  cbn in He. injection He as Eab Elr. subst b. cbn [memcmp_model]. rewrite Z.eqb_refl.
  apply IH; cbn in *; [lia | lia | exact Elr].
Qed.

(** Replace one cell of a cell list by cells that hold the same bytes. *)
Lemma chk_cells_at_replace : forall segs m A pre c new post,
  cells_at segs m A (pre ++ c :: post) -> cells_wf new -> cells_bytes new = cbytes c ->
  cells_at segs m A (pre ++ new ++ post).
Proof.
  intros segs m A pre c new post [Hwf Hb] Hw Hn. split.
  - apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|].
    apply cells_wf_app. split; assumption.
  - rewrite !cells_bytes_app in *. rewrite Hn. cbn [cells_bytes] in Hb. exact Hb.
Qed.

(** A 4-byte little-endian value read back as its bytes. *)
Lemma chk_le4_key : forall b0 b1 b2 b3 : byte,
  le4 (Z_to_bv 64 (fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 [b0; b1; b2; b3])) = [b0; b1; b2; b3].
Proof.
  intros. apply le4_of_mod32; [reflexivity|].
  pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
  cbn [fold_right map le_val].
  rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

(** The 32 bytes of a struct diginet_cmd as cells: bytes[24], len, display, padding, key. *)
Definition chk_out_cells (out : list byte) : list cell :=
  [CB 24 (firstn 24 out); C1 (nth 24 out (Z_to_bv 8 0)); C1 (nth 25 out (Z_to_bv 8 0));
   CB 2 (firstn 2 (skipn 26 out));
   C4 (Z_to_bv 64 (fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 (firstn 4 (skipn 28 out))))].

Lemma chk_out_cells_ok : forall out : list byte, length out = 32%nat ->
  cells_wf (chk_out_cells out) /\ cells_bytes (chk_out_cells out) = out.
Proof.
  intros out L.
  do 32 (destruct out as [|? out]; [discriminate L|]).
  destruct out; [|discriminate L].
  split; [cbn; repeat split|].
  cbn [chk_out_cells cells_bytes cbytes firstn skipn nth app].
  rewrite chk_le4_key. reflexivity.
Qed.
