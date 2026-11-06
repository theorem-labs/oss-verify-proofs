(** Word, memory and answer facts the walks of headamp_dup_pod, headamp_dup_first and headamp_plain
    (U/Prog/LLVMFuzzerTestOneInput_c.v) share: the compiled tests on literal words, the byte a `lbu` reads from an
    8-byte cell, the bytes of a block a callee filled, and the length of the parse's cells. No function of a binary
    is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** The return address of a call is even. *)
Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).

(** A disjunction lia does not split: a walk unfolds it only where a bound needs it. *)
Definition or_h (P Q : Prop) : Prop := P \/ Q.
Lemma or_hide : forall P Q : Prop, P \/ Q -> or_h P Q.
Proof. intros P Q H. exact H. Qed.

(** ** Compiled tests on literal words *)
Lemma eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma signed_lit : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - replace (x mod 2^64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
    destruct (Z.ltb_spec (x + 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec x (2^63)); lia.
Qed.

Lemma lts_s : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

(** ** The byte `lbu` reads at an 8-byte cell *)
Lemma firstn_le8 : forall v : word, firstn 1 (le8 v) = le1 v.
Proof. intros v. reflexivity. Qed.

Lemma read_byte0 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 1 = Some (le1 v).
Proof.
  intros m a v H. pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 1 H) as R.
  rewrite length_le8, Z.add_0_r in R. rewrite R by lia. rewrite <- firstn_le8. reflexivity.
Qed.

Lemma zx8_small : forall z, 0 <= z < 256 -> zx8 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx8. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(** ** Blocks a callee filled *)
Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma rw_cells_CB_wr : forall m A n bs, rw_cells rsegs m A [CB n bs] -> wr_at rsegs m A (Z.of_nat n).
Proof. intros m A n bs [_ W]. cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. exact W. Qed.

(** ** The parse's cells: 3 bytes per cell, none when it fails *)
Lemma cells_len : forall cap o, 0 <= cap -> answer_ok cap o ->
  Z.of_nat (length (ha_cells_bytes (ans_cells o))) = 3 * Z.max (ans_rc o) 0 /\ -1 <= ans_rc o <= cap /\
  Z.of_nat (length (ans_cells o)) = Z.max (ans_rc o) 0.
Proof.
  intros cap o Hc HO. rewrite length_ha_cells_bytes.
  apply answer_ok_parts in HO as [[(E1 & E2 & _) | (E1 & E2 & _)] _].
  - rewrite E2. cbn [length]. lia.
  - lia.
Qed.
