(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LV (V : nat -> Z) (i : nat) : Z :=
  if Nat.eqb i 6 then 256 * V 10%nat + V 6%nat
  else if Nat.eqb i 42 then V 44%nat else if Nat.eqb i 91 then V 78%nat
  else if Nat.eqb i 220 then V 207%nat else if Nat.eqb i 221 then V 208%nat else if Nat.eqb i 222 then V 209%nat
  else if Nat.eqb i 239 then V 226%nat else if Nat.eqb i 240 then V 227%nat else if Nat.eqb i 241 then V 228%nat
  else if Nat.eqb i 258 then V 245%nat else if Nat.eqb i 323 then V 310%nat else if Nat.eqb i 357 then V 344%nat
  else if Nat.eqb i 406 then V 377%nat else if Nat.eqb i 485 then V 453%nat else if Nat.eqb i 486 then V 454%nat
  else if Nat.eqb i 503 then V 471%nat else if Nat.eqb i 584 then V 471%nat
  else if Nat.eqb i 617 then V 664%nat else if Nat.eqb i 618 then V 665%nat else if Nat.eqb i 619 then V 666%nat
  else if Nat.eqb i 620 then V 667%nat else if Nat.eqb i 621 then V 668%nat else if Nat.eqb i 622 then V 669%nat
  else if Nat.eqb i 623 then V 670%nat else if Nat.eqb i 624 then V 671%nat else if Nat.eqb i 625 then V 672%nat
  else if Nat.eqb i 626 then V 673%nat else if Nat.eqb i 627 then V 674%nat
  else if Nat.eqb i 484 then V 452%nat else if Nat.eqb i 324 then V 311%nat
  else V i.
(* [comment removed for export] *)
Lemma LV_sp0 : forall V w U, al_sp0 (mkALayout (LV V) w U) = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.
Proof. intros. unfold al_sp0. cbn [al_V LV Nat.eqb]. lia. Qed.
Lemma LV_t : forall V w U, al_t (mkALayout (LV V) w U) = 4096 * V 227%nat.
Proof. reflexivity. Qed.
Lemma LV_ctx : forall V w U, al_ctx (mkALayout (LV V) w U) = 4096 * V 228%nat.
Proof. reflexivity. Qed.
Lemma LV_space_beg : forall V w U, al_space_beg (mkALayout (LV V) w U) = 4096 * (V 208%nat - V 209%nat) + 0x10000.
Proof. reflexivity. Qed.
Lemma LV_ptr_array : forall V w U, al_ptr_array (mkALayout (LV V) w U) = 4096 * V 226%nat.
Proof. reflexivity. Qed.
Lemma LV_nodes : forall V w U, al_nodes (mkALayout (LV V) w U) = 4096 * V 453%nat.
Proof. reflexivity. Qed.
Lemma LV_store : forall V w U, al_store (mkALayout (LV V) w U) = 4096 * V 454%nat.
Proof. reflexivity. Qed.
Lemma LV_fake : forall V w U, al_fake (mkALayout (LV V) w U) = 4096 * V 377%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition pfact_eqb' (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'   (* [comment removed for export] *)
  | _, _ => false
  end.
Lemma pfact_eqb'_eq : forall f g, pfact_eqb' f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find' : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb' f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb'_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (pfact_find' V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.
Ltac mwr V m HM a n H := pose proof (mwr_find bsegs V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.
Ltac mimg V m HM lo hi H := pose proof (mimg_cover bsegs V m _ lo hi HM ltac:(vm_compute; reflexivity)) as H.
(* [comment removed for export] *)
Section CANSEC1b. Context {rc : runConstT}.
Lemma mwrs_find : forall V m (l : list mfact) a n,
  Forall (mfact_ok bsegs V m) l ->
  existsb (fun f => match f with MWrS a' n' => zexp_eqb a' a && zexp_eqb n' n | _ => false end) l = true ->
  wr_at bsegs m (zv V a) (zv V n).
Proof.
  intros V m l a n HF HE. apply existsb_exists in HE as (f & Hin & Hf).
  destruct f; try discriminate. apply andb_prop in Hf as [H1 H2]. apply zexp_eqb_eq in H1. apply zexp_eqb_eq in H2. subst.
  exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
End CANSEC1b.
Ltac mwrs V m HM a n H := pose proof (mwrs_find V m _ a n HM ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma bytes_eq_of_unsigned' : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at bsegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zshape (cs : list cell) : bool :=
  match cs with
  | [] => true
  | C1 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C2 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C4 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | C8 v :: cs' => Z.eqb (bv_unsigned v) 0 && zshape cs'
  | CB n bs :: cs' => Nat.eqb (length bs) n && forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs && zshape cs'
  end.

Lemma repeat_zero_eq : forall (bs : list byte), forallb (fun b : byte => Z.eqb (bv_unsigned b) 0) bs = true ->
  bs = repeat (Z_to_bv 8 0) (length bs).
Proof.
  induction bs as [|b bs IH]; cbn; intros H; [reflexivity|]. apply andb_prop in H as [H1 H2].
  f_equal; [| apply IH; exact H2]. apply bv_eq. apply Z.eqb_eq in H1. rewrite H1. reflexivity.
Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.
Lemma le2_zero : le2 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 2.
Proof. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

Lemma word_zero_eq : forall v : word, (bv_unsigned v =? 0) = true -> v = Z_to_bv 64 0.
Proof. intros v H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.
Lemma byte_zero_eq : forall b : byte, (bv_unsigned b =? 0) = true -> b = Z_to_bv 8 0.
Proof. intros b H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma cbytes_zero : forall c, zshape [c] = true -> cbytes c = repeat (Z_to_bv 8 0) (csize c) /\ cells_wf [c].
Proof.
  intros c H. destruct c as [v|v|v|v|n bs]; cbn [zshape] in H; rewrite ?andb_true_r in H.
  - apply word_zero_eq in H. subst v. split; [exact le8_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le4_zero| cbn; split; exact I].
  - apply word_zero_eq in H. subst v. split; [exact le2_zero| cbn; split; exact I].
  - apply byte_zero_eq in H. subst v. split; [reflexivity| cbn; split; exact I].
  - apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. split; [| cbn; split; [exact H1| exact I]].
    cbn [cbytes csize]. rewrite (repeat_zero_eq bs H2) at 1. rewrite H1. reflexivity.
Qed.

Lemma zshape_bytes : forall cs, zshape cs = true ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) /\ cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [split; [reflexivity| exact I]|].
  assert (Hc : zshape [c] = true /\ zshape cs = true).
  { destruct c; cbn in H |- *; repeat (apply andb_prop in H as [H ?]); rewrite ?andb_true_r; auto.
    split; [apply andb_true_intro; split; assumption| assumption]. }
  destruct Hc as [Hc Hcs]. destruct (cbytes_zero c Hc) as [Ec Wc]. destruct (IH Hcs) as [Ecs Wcs].
  split.
  - cbn [cells_bytes cells_size]. rewrite Ec, Ecs, <- repeat_app. reflexivity.
  - destruct c; cbn in Wc |- *; tauto.
Qed.

(* [comment removed for export] *)
Lemma zcells : forall m A cs,
  zshape cs = true ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m (wa (A + i)) = Some (Z_to_bv 8 0)) ->
  wr_at bsegs m A (Z.of_nat (cells_size cs)) ->
  rw_cells bsegs m A cs.
Proof.
  intros m A cs Hz Z0 W. destruct (zshape_bytes cs Hz) as [E WF].
  eapply rw_cells_recast; [apply (mzero_rw_cells bsegs m A (Z.of_nat (cells_size cs))); [exact Z0| exact W| lia]| exact WF| |].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, E. unfold zeros. rewrite Nat2Z.id. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Definition byte_zero (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_zero s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_zero in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge]; [exact (IH _ _ H1 i Hl)|].
      specialize (IH _ _ H2 (i - h)%N ltac:(lia)). replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

End CANSEC2.
Notation S3 := AsanUbsan_seg_bytes_003 (only parsing).
Section CANSEC3. Context {rc : runConstT}.
Definition SEG3 : Z := 0xb3000.

Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma a_find_segment_3 : forall i, 0xb3000 <= i < 0x60f000 -> find_segment bsegs i 1 = Some AsanUbsan_segment_003.
Proof.
  intros i Hi. rewrite a_find_segment_1 by lia.
  destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x30000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0x30000 i); destruct (Z.leb_spec0 (i + 1) 0xb1000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xb1000 i); destruct (Z.leb_spec0 (i + 1) 0xb3000); cbn [andb]; try lia.
  destruct (Z.leb_spec0 0xb3000 i); destruct (Z.leb_spec0 (i + 1) 0x60f000); cbn [andb]; try lia. reflexivity.
Qed.
Lemma seg3_base : Z.of_N (seg_base AsanUbsan_segment_003) = 0xb3000.
Proof. vm_compute. reflexivity. Qed.
Lemma seg3_readable : seg_readable AsanUbsan_segment_003 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma img_zero_run : forall (off n : N) m lo,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xb3000 + Z.of_N off -> lo + Z.of_N n <= 0x60f000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) ->
  forall i, 0 <= i < Z.of_N n -> mrd bsegs m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
  intros off n m lo SC -> Hhi Hnone i Hi.
  unfold mrd. rewrite (Hnone (0xb3000 + Z.of_N off + i)) by lia.
  unfold seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
  rewrite (a_find_segment_3 (0xb3000 + Z.of_N off + i)) by lia. rewrite seg3_readable, seg3_base. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes seg_bytes AsanUbsan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (Z.to_N (0xb3000 + Z.of_N off + i - 0xb3000) <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  replace (Z.to_N (0xb3000 + Z.of_N off + i - 0xb3000)) with (off + Z.to_N i)%N by lia.
  rewrite (zscanN_sound _ 64 off n SC (Z.to_N i)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma img_zero_stk : forall (off n : N) m lo,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xb3000 + Z.of_N off -> lo + Z.of_N n <= 0x60f000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at bsegs m lo (Z.of_N n) ->
  stk bsegs m lo (lo + Z.of_N n).
Proof.
  intros off n m lo SC Hlo Hhi Hnone W. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  destruct W as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros a Ha.
  split; [replace a with (lo + (a - lo)) by lia; apply W3; lia|].
  exists (Z_to_bv 8 0). replace a with (lo + (a - lo)) by lia. apply R. lia.
Qed.

Lemma img_zero_bytes_at : forall (off n : N) m lo k,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xb3000 + Z.of_N off -> lo + Z.of_N n <= 0x60f000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> (Z.of_nat k <= Z.of_N n) ->
  bytes_at bsegs m lo (repeat (Z_to_bv 8 0) k).
Proof.
  intros off n m lo k SC Hlo Hhi Hnone Hk. pose proof (img_zero_run off n m lo SC Hlo Hhi Hnone) as R.
  split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). apply R. lia.
Qed.

Lemma img_zero_cells : forall (off n : N) m lo cs,
  zscanN AsanUbsan_seg_bytes_003 64 off n = true ->
  lo = 0xb3000 + Z.of_N off -> lo + Z.of_N n <= 0x60f000 ->
  (forall i, lo <= i < lo + Z.of_N n -> m (wa i) = None) -> wr_at bsegs m lo (Z.of_nat (cells_size cs)) ->
  zshape cs = true -> Z.of_nat (cells_size cs) <= Z.of_N n ->
  rw_cells bsegs m lo cs.
Proof.
  intros off n m lo cs SC Hlo Hhi Hnone W Hz Hsz. destruct (zshape_bytes cs Hz) as [E WF].
  split; [split; [exact WF|]| exact W]. rewrite E. eapply img_zero_bytes_at; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_CB0 : forall m A, 0 <= A -> A <= 2^64 -> rw_cells bsegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn. unfold bytes_at. cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - cbn. unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr bsegs m A [].
Proof. intros m A H0 H1. unfold u32arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

Lemma u64arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u64arr bsegs m A [].
Proof. intros m A H0 H1. unfold u64arr, bytes_at, wr_at. cbn. repeat split; intros; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32s_zero : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u32s flat_map]. rewrite IH.
  replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app, le4_zero. reflexivity.
Qed.
Lemma u64s_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s flat_map]. rewrite IH.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app, le8_zero. reflexivity.
Qed.

Lemma bytes_at_zero : forall m A n,
  (forall i, 0 <= i < Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  bytes_at bsegs m A (repeat (Z_to_bv 8 0) n).
Proof.
  intros m A n Z0 H0 H1. split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
  rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). unfold mrd. rewrite (Z0 (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

Lemma u32arr_zero : forall m A n,
  (forall i, 0 <= i < 4 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at bsegs m A (4 * Z.of_nat n) ->
  u32arr bsegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. pose proof W as (W1 & W2 & _). split; [| rewrite repeat_length; exact W].
  rewrite u32s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

Lemma u64arr_zero : forall m A n,
  (forall i, 0 <= i < 8 * Z.of_nat n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at bsegs m A (8 * Z.of_nat n) ->
  u64arr bsegs m A (repeat (Z_to_bv 64 0) n).
Proof.
  intros m A n Z0 W. pose proof W as (W1 & W2 & _). split; [| rewrite repeat_length; exact W].
  rewrite u64s_zero. apply bytes_at_zero; [| lia| lia]. intros i Hi. apply Z0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_cell : forall m A (bs : list byte) (v : Z),
  (forall i, A <= i < A + 8 -> m (wa i) = None) ->
  length bs = 8%nat -> rw_bytes_b bsegs A bs = true -> bs = le8 (Z_to_bv 64 v) -> 0 <= A -> A + 8 <= 2^64 ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A bs v Hm Hl Hb Hbs H0 H1.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A bs)| cbn; split; [reflexivity| exact I]| |].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply Hm. rewrite Hl in Ha. lia.
  - exact Hb. - lia. - rewrite Hl. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, Hbs. reflexivity.
  - cbn. rewrite Hl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_chunk : forall V m (l : list mfact) A cs,
  Forall (mfact_ok bsegs V m) l ->
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
  cells_wf cs -> rw_bytes_b bsegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
  rw_cells bsegs m A cs.
Proof.
  intros V m l A cs HM HE WF HB HA HHI.
  pose proof (cells_bytes_length cs WF) as LEN.
  assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
  { eapply mimg_cover; [exact HM| exact HE]. }
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
  - intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. lia.
  - exact HB.
  - exact HA.
  - rewrite LEN. exact HHI.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac aimg V m HM A cs H :=
  pose proof (img_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Lemma rw_cells_cons : forall m A c cs,
  rw_cells bsegs m A [c] -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs -> rw_cells bsegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app bsegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.
Lemma rw_cells_hd : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [H _]. exact H. Qed.
Lemma rw_cells_tl : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.

(* [comment removed for export] *)
End CANSEC4.
Ltac recast H := eapply rw_cells_recast; [exact H| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned'; vm_compute; reflexivity| reflexivity].
