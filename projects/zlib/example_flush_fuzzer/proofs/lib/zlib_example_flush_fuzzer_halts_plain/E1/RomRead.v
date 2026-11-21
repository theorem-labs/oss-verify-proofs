(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 MemRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Lemma u_bv1 : bv_unsigned (1 : word) = 1.
Proof. reflexivity. Qed.

Lemma Z2bv_add1 : forall z : Z, (Z_to_bv 64 z + 1)%bv = Z_to_bv 64 (z + 1).
Proof.
  intro z. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, u_bv1.
  rewrite bv_wrap_add_idemp_l. reflexivity.
Qed.


Definition chk_rom (segs : list Segment) (base : Z) (g : Z -> byte) (n : nat) : bool :=
  forallb (fun j => match seg_rom segs (Z_to_bv 64 (base + Z.of_nat j)) with
                    | Some b => bv_eqb b (g (Z.of_nat j))
                    | None => false
                    end) (seq 0 n).

Lemma chk_rom_sound : forall segs base g n j,
  chk_rom segs base g n = true -> 0 <= j < Z.of_nat n ->
  seg_rom segs (Z_to_bv 64 (base + j)) = Some (g j).
Proof.
  intros segs base g n j H Hj.
  unfold chk_rom in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat j)).
  rewrite Z2Nat.id in H by lia.
  assert (Hin : In (Z.to_nat j) (seq 0 n)) by (apply in_seq; lia).
  specialize (H Hin).
  destruct (seg_rom segs (Z_to_bv 64 (base + j))) as [b|]; [|discriminate].
  apply bv_eqb_eq in H. rewrite H. reflexivity.
Qed.

Definition rom_clear (mem : word -> option byte) (lo hi : Z) : Prop :=
  forall x : word, lo <= bv_unsigned x < hi -> mem x = None.


Lemma rom_clear_wbytes : forall mem lo hi (b : Z) bs,
  rom_clear mem lo hi ->
  (forall x : word, b <= bv_unsigned x < b + Z.of_nat (length bs) -> mem x <> None) ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  rom_clear (wbytes mem (zw b) bs) lo hi.
Proof.
  intros mem lo hi b bs Hc Hm Hb0 Hb1 x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) b) as [L|L];
    [|destruct (Z_lt_le_dec (bv_unsigned x) (b + Z.of_nat (length bs))) as [L2|L2]].
  - rewrite wbytes_inside; [apply Hc; exact Hx | lia | lia | lia].
  - exfalso. apply (Hm x ltac:(lia)). apply Hc. exact Hx.
  - rewrite wbytes_inside; [apply Hc; exact Hx | lia | lia | lia].
Qed.

Lemma in_franges_dec : forall F x, in_franges F x \/ ~ in_franges F x.
Proof.
  intros F x. induction F as [|[lo n] F' IH]; [right; intros H; exact H|].
  cbn [in_franges]. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x (lo + n)); destruct IH as [H|H];
    first [ left; left; lia | left; right; exact H | right; intros [H'|H']; [lia | exact (H H')] ].
Qed.

Lemma rom_clear_agree : forall F mem m lo hi,
  rom_clear mem lo hi -> agree_out F mem m ->
  (forall x : word, in_franges F (bv_unsigned x) -> mem x <> None) ->
  rom_clear m lo hi.
Proof.
  intros F mem m lo hi Hc Hag HF x Hx.
  destruct (in_franges_dec F (bv_unsigned x)) as [Hin|Hout].
  - exfalso. apply (HF _ Hin). apply Hc. exact Hx.
  - rewrite (Hag x Hout). apply Hc. exact Hx.
Qed.

Lemma mapped_clear_apart : forall m lo n clo chi,
  rom_clear m clo chi -> (forall x : word, lo <= bv_unsigned x < lo + n -> m x <> None) ->
  0 <= lo -> lo + n <= 2 ^ 64 -> 0 <= clo -> chi <= 2 ^ 64 ->
  lo + n <= clo \/ chi <= lo \/ n <= 0 \/ chi <= clo.
Proof.
  intros m lo n clo chi Hc Hm Hlo Hhi Hc0 Hc1.
  destruct (Z_le_gt_dec n 0) as [|Hn]; [lia|].
  destruct (Z_le_gt_dec chi clo) as [|Hcc]; [lia|].
  destruct (Z_le_gt_dec (lo + n) clo) as [|H1]; [lia|].
  destruct (Z_le_gt_dec chi lo) as [|H2]; [lia|].
  exfalso.
  set (x := Z.max lo clo).
  apply (Hm (zw x)); [rewrite u_zw_small; subst x; lia|].
  apply Hc. rewrite u_zw_small; subst x; lia.
Qed.

Definition wr_ok (m M : word -> option byte) : Prop := forall x : word, m x = None -> M x = None.

Lemma wr_ok_refl : forall m, wr_ok m m.
Proof. intros m x H. exact H. Qed.


Lemma wr_ok_wbytes : forall m M (b : Z) bs,
  wr_ok m M -> (forall x : word, b <= bv_unsigned x < b + Z.of_nat (length bs) -> m x <> None) ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  wr_ok m (wbytes M (zw b) bs).
Proof.
  intros m M b bs HW Hm Hb0 Hb1 x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) b) as [L|L];
    [|destruct (Z_lt_le_dec (bv_unsigned x) (b + Z.of_nat (length bs))) as [L2|L2]].
  - rewrite wbytes_inside; [apply HW; exact Hx | lia | lia | lia].
  - exfalso. exact (Hm x ltac:(lia) Hx).
  - rewrite wbytes_inside; [apply HW; exact Hx | lia | lia | lia].
Qed.



Lemma rom_clear_wr : forall m M lo hi, rom_clear m lo hi -> wr_ok m M -> rom_clear M lo hi.
Proof. intros m M lo hi Hc HW x Hx. apply HW. apply Hc. exact Hx. Qed.



Definition tab8_byte (f : Z -> Z) (j : Z) : byte := Z_to_bv 8 (f j).

Definition tab32_byte (f : Z -> Z) (j : Z) : byte :=
  nth (Z.to_nat (j mod 4)) (Z_to_le_bytes 4 (f (j / 4))) (Z_to_bv 8 0).

Definition tab64_byte (f : Z -> Z) (j : Z) : byte :=
  nth (Z.to_nat (j mod 8)) (Z_to_le_bytes 8 (f (j / 8))) (Z_to_bv 8 0).

Definition ct_byte (fc dl : Z -> Z) (j : Z) : byte :=
  let i := j / 4 in
  let r := j mod 4 in
  if r =? 0 then Z_to_bv 8 (fc i)
  else if r =? 1 then Z_to_bv 8 (Z.shiftr (fc i) 8)
  else if r =? 2 then Z_to_bv 8 (dl i)
  else Z_to_bv 8 (Z.shiftr (dl i) 8).

Lemma divmod4 : forall i k, 0 <= i -> 0 <= k < 4 -> (4 * i + k) mod 4 = k /\ (4 * i + k) / 4 = i.
Proof.
  intros i k Hi Hk. split.
  - rewrite Z.add_comm, Z.mul_comm, Z.mod_add, Z.mod_small; lia.
  - rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small; lia.
Qed.

Lemma divmod8 : forall i k, 0 <= i -> 0 <= k < 8 -> (8 * i + k) mod 8 = k /\ (8 * i + k) / 8 = i.
Proof.
  intros i k Hi Hk. split.
  - rewrite Z.add_comm, Z.mul_comm, Z.mod_add, Z.mod_small; lia.
  - rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small; lia.
Qed.

Section Rod.
Variable segs : list Segment.
Variable mem : word -> option byte.

Lemma tab_cell1 : forall A f (n : nat) i,
  chk_rom segs A (tab8_byte f) n = true ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + i) 1 (f i).
Proof.
  intros A f n i Hchk Hnone Hi HA HAn. unfold cell. cbn [rdn Z_to_le_bytes].
  rewrite (Hnone (zw (A + i))) by (rewrite u_zw_small; lia).
  change (zw (A + i)) with (Z_to_bv 64 (A + i)).
  rewrite (chk_rom_sound _ _ _ _ i Hchk) by lia. reflexivity.
Qed.

Lemma tab_cell4 : forall A f (n : nat) i,
  chk_rom segs A (tab32_byte f) (4 * n) = true ->
  (forall x : word, A <= bv_unsigned x < A + 4 * Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + 4 * Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + 4 * i) 4 (f i).
Proof.
  intros A f n i Hchk Hnone Hi HA HAn. unfold cell.
  assert (N : forall k, 0 <= k < 4 -> mem (Z_to_bv 64 (A + (4 * i + k))) = None).
  { intros k Hk. apply Hnone. change (Z_to_bv 64 (A + (4 * i + k))) with (zw (A + (4 * i + k))).
    rewrite u_zw_small; lia. }
  assert (R : forall k, 0 <= k < 4 ->
    seg_rom segs (Z_to_bv 64 (A + (4 * i + k))) = Some (nth (Z.to_nat k) (Z_to_le_bytes 4 (f i)) (Z_to_bv 8 0))).
  { intros k Hk. rewrite (chk_rom_sound _ _ _ _ (4 * i + k) Hchk) by lia.
    unfold tab32_byte. destruct (divmod4 i k ltac:(lia) Hk) as [-> ->]. reflexivity. }
  cbn [rdn]. unfold zw.
  replace (Z_to_bv 64 (A + 4 * i)) with (Z_to_bv 64 (A + (4 * i + 0))) by (f_equal; lia).
  rewrite (N 0), (R 0) by lia.
  rewrite Z2bv_add1. replace (A + (4 * i + 0) + 1) with (A + (4 * i + 1)) by lia. rewrite (N 1), (R 1) by lia.
  rewrite Z2bv_add1. replace (A + (4 * i + 1) + 1) with (A + (4 * i + 2)) by lia. rewrite (N 2), (R 2) by lia.
  rewrite Z2bv_add1. replace (A + (4 * i + 2) + 1) with (A + (4 * i + 3)) by lia. rewrite (N 3), (R 3) by lia.
  reflexivity.
Qed.

Lemma tab_cell8 : forall A f (n : nat) i,
  chk_rom segs A (tab64_byte f) (8 * n) = true ->
  (forall x : word, A <= bv_unsigned x < A + 8 * Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + 8 * Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + 8 * i) 8 (f i).
Proof.
  intros A f n i Hchk Hnone Hi HA HAn. unfold cell.
  assert (N : forall k, 0 <= k < 8 -> mem (Z_to_bv 64 (A + (8 * i + k))) = None).
  { intros k Hk. apply Hnone. change (Z_to_bv 64 (A + (8 * i + k))) with (zw (A + (8 * i + k))).
    rewrite u_zw_small; lia. }
  assert (R : forall k, 0 <= k < 8 ->
    seg_rom segs (Z_to_bv 64 (A + (8 * i + k))) = Some (nth (Z.to_nat k) (Z_to_le_bytes 8 (f i)) (Z_to_bv 8 0))).
  { intros k Hk. rewrite (chk_rom_sound _ _ _ _ (8 * i + k) Hchk) by lia.
    unfold tab64_byte. destruct (divmod8 i k ltac:(lia) Hk) as [-> ->]. reflexivity. }
  cbn [rdn]. unfold zw.
  replace (Z_to_bv 64 (A + 8 * i)) with (Z_to_bv 64 (A + (8 * i + 0))) by (f_equal; lia).
  rewrite (N 0), (R 0) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 0) + 1) with (A + (8 * i + 1)) by lia. rewrite (N 1), (R 1) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 1) + 1) with (A + (8 * i + 2)) by lia. rewrite (N 2), (R 2) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 2) + 1) with (A + (8 * i + 3)) by lia. rewrite (N 3), (R 3) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 3) + 1) with (A + (8 * i + 4)) by lia. rewrite (N 4), (R 4) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 4) + 1) with (A + (8 * i + 5)) by lia. rewrite (N 5), (R 5) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 5) + 1) with (A + (8 * i + 6)) by lia. rewrite (N 6), (R 6) by lia.
  rewrite Z2bv_add1. replace (A + (8 * i + 6) + 1) with (A + (8 * i + 7)) by lia. rewrite (N 7), (R 7) by lia.
  reflexivity.
Qed.

Lemma ct_cell_fc : forall A fc dl (n : nat) i,
  chk_rom segs A (ct_byte fc dl) (4 * n) = true ->
  (forall x : word, A <= bv_unsigned x < A + 4 * Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + 4 * Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + 4 * i) 2 (fc i).
Proof.
  intros A fc dl n i Hchk Hnone Hi HA HAn. unfold cell.
  assert (N : forall k, 0 <= k < 4 -> mem (Z_to_bv 64 (A + (4 * i + k))) = None).
  { intros k Hk. apply Hnone. change (Z_to_bv 64 (A + (4 * i + k))) with (zw (A + (4 * i + k))).
    rewrite u_zw_small; lia. }
  assert (R : forall k, 0 <= k < 4 ->
    seg_rom segs (Z_to_bv 64 (A + (4 * i + k))) = Some (ct_byte fc dl (4 * i + k))).
  { intros k Hk. rewrite (chk_rom_sound _ _ _ _ (4 * i + k) Hchk) by lia. reflexivity. }
  cbn [rdn]. unfold zw.
  replace (Z_to_bv 64 (A + 4 * i)) with (Z_to_bv 64 (A + (4 * i + 0))) by (f_equal; lia).
  rewrite (N 0), (R 0) by lia.
  rewrite Z2bv_add1. replace (A + (4 * i + 0) + 1) with (A + (4 * i + 1)) by lia. rewrite (N 1), (R 1) by lia.
  unfold ct_byte. destruct (divmod4 i 0 ltac:(lia) ltac:(lia)) as [-> ->].
  destruct (divmod4 i 1 ltac:(lia) ltac:(lia)) as [-> ->]. cbn [Z.eqb Pos.eqb].
  reflexivity.
Qed.

Lemma ct_cell_dl : forall A fc dl (n : nat) i,
  chk_rom segs A (ct_byte fc dl) (4 * n) = true ->
  (forall x : word, A <= bv_unsigned x < A + 4 * Z.of_nat n -> mem x = None) ->
  0 <= i < Z.of_nat n -> 0 <= A -> A + 4 * Z.of_nat n < 2 ^ 64 ->
  cell segs mem (A + 4 * i + 2) 2 (dl i).
Proof.
  intros A fc dl n i Hchk Hnone Hi HA HAn. unfold cell.
  assert (N : forall k, 0 <= k < 4 -> mem (Z_to_bv 64 (A + (4 * i + k))) = None).
  { intros k Hk. apply Hnone. change (Z_to_bv 64 (A + (4 * i + k))) with (zw (A + (4 * i + k))).
    rewrite u_zw_small; lia. }
  assert (R : forall k, 0 <= k < 4 ->
    seg_rom segs (Z_to_bv 64 (A + (4 * i + k))) = Some (ct_byte fc dl (4 * i + k))).
  { intros k Hk. rewrite (chk_rom_sound _ _ _ _ (4 * i + k) Hchk) by lia. reflexivity. }
  cbn [rdn]. unfold zw.
  replace (Z_to_bv 64 (A + 4 * i + 2)) with (Z_to_bv 64 (A + (4 * i + 2))) by (f_equal; lia).
  rewrite (N 2), (R 2) by lia.
  rewrite Z2bv_add1. replace (A + (4 * i + 2) + 1) with (A + (4 * i + 3)) by lia. rewrite (N 3), (R 3) by lia.
  unfold ct_byte. destruct (divmod4 i 2 ltac:(lia) ltac:(lia)) as [-> ->].
  destruct (divmod4 i 3 ltac:(lia) ltac:(lia)) as [-> ->]. cbn [Z.eqb Pos.eqb].
  reflexivity.
Qed.

End Rod.
End FXG.
