(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie ExLin ExVal ExBytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Inductive abyte : Type :=
| BL (b : int)
| BT
| BF (v : aval) (i : nat).

Definition abyte_val (ρ : valuation) (ab : abyte) (b : byte) : Prop :=
  match ab with
  | BL x => bv_unsigned b = to_Z x
  | BT => True
  | BF v i => exists w : bv 64, aval_val ρ v w /\ bv_unsigned b = zbyte (bv_unsigned w) i
  end.

Inductive cell : Type :=
| CW (w : w64)
| CB (l : list abyte).

Definition cbyte (c : cell) (i : nat) : abyte :=
  match c with
  | CW w => BL (w_byte w i)
  | CB l => nth i l BT
  end.

Definition zero_cell : cell := CW w_zero.
Definition unk_cell : cell := CB (repeat BT 8).

Inductive rkind : Type :=
| KZero
| KUnk
| KImg (w : bool)
| KZL (l : list (int * int))
| KWin (f : lin).

Record region : Type := Rg {
  rg_lo : int;
  rg_hi : int;
  rg_kind : rkind;
  rg_d : nat;
  rg_cells : itrie cell
}.

Definition rk_writable (k : rkind) : bool :=
  match k with KZero | KUnk | KZL _ | KWin _ => true | KImg w => w end.

Definition is_win (k : rkind) : bool := match k with KWin _ => true | _ => false end.

Definition inl (l : list (int * int)) (a : Z) : bool := existsb (fun p => (to_Z (fst p) <=? a) && (a <? to_Z (snd p))) l.

Section WithSegs.
Variable segs : list Segment.

Definition wz (a : Z) : word := Z_to_bv 64 a.

Definition img_byte (a : Z) : abyte :=
  match seg_rom segs (wz a) with Some b => BL (of_Z (bv_unsigned b)) | None => BT end.

Definition default_byte (k : rkind) (a : Z) : abyte :=
  match k with
  | KZero => BL 0%uint63
  | KUnk => BT
  | KImg _ => img_byte a
  | KZL l => if inl l a then BT else BL 0%uint63
  | KWin _ => BT
  end.

Definition default_cell (k : rkind) (a : Z) : cell :=
  match k with
  | KZero => zero_cell
  | KUnk => unk_cell
  | KImg _ => CB (map (fun i => img_byte (a + Z.of_nat i)) (seq 0 8))
  | KZL l => if existsb (fun p => (a <? to_Z (snd p)) && (to_Z (fst p) <? a + 8)) l
             then CB (map (fun i => if inl l (a + Z.of_nat i) then BT else BL 0%uint63) (seq 0 8)) else zero_cell
  | KWin _ => unk_cell
  end.

Definition cell_key (R : region) (x : int) : int := ((x - rg_lo R) >> 3)%uint63.

Definition int8_nat (i : int) : nat :=
  if (i =? 0)%uint63 then 0%nat else if (i =? 1)%uint63 then 1%nat else if (i =? 2)%uint63 then 2%nat
  else if (i =? 3)%uint63 then 3%nat else if (i =? 4)%uint63 then 4%nat else if (i =? 5)%uint63 then 5%nat
  else if (i =? 6)%uint63 then 6%nat else 7%nat.
Definition cell_off (R : region) (x : int) : nat := int8_nat ((x - rg_lo R) land 7)%uint63.

Definition in_region (R : region) (x : int) : bool := (rg_lo R <=? x)%uint63 && (x <? rg_hi R)%uint63.

Definition get_cell (R : region) (k : int) : cell :=
  match iget (rg_d R) (rg_cells R) k with
  | Some c => c
  | None => default_cell (rg_kind R) (to_Z (rg_lo R) + 8 * to_Z k)
  end.

Definition rbyte (R : region) (x : int) : abyte :=
  cbyte (get_cell R (cell_key R x)) (cell_off R x).

Fixpoint aview (A : list region) (x : int) : option (abyte * bool) :=
  match A with
  | [] => None
  | R :: A' => if in_region R x then (if is_win (rg_kind R) then None else Some (rbyte R x, rk_writable (rg_kind R))) else aview A' x
  end.

Definition rv (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

Definition region_wf (R : region) : Prop :=
  0 <= to_Z (rg_lo R) /\ to_Z (rg_lo R) <= to_Z (rg_hi R) /\ to_Z (rg_hi R) < 2 ^ 47
  /\ to_Z (rg_lo R) mod 8 = 0 /\ to_Z (rg_hi R) - to_Z (rg_lo R) <= 8 * 2 ^ Z.of_nat (rg_d R)
  /\ (rg_d R <= 44)%nat.

Definition rdisj (R1 R2 : region) : Prop :=
  to_Z (rg_hi R1) <= to_Z (rg_lo R2) \/ to_Z (rg_hi R2) <= to_Z (rg_lo R1).

Fixpoint regions_ok (A : list region) : Prop :=
  match A with
  | [] => True
  | R :: A' => region_wf R /\ Forall (rdisj R) A' /\ regions_ok A'
  end.

Definition RWin (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  forall R f, In R A -> rg_kind R = KWin f ->
    forall x : Z, to_Z (rg_lo R) <= x < to_Z (rg_hi R) -> x < to_Z (rg_lo R) + leval ρ f -> m (wz x) <> None.

Definition RMem (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  regions_ok A /\
  (forall (x : int) (ab : abyte) (w : bool), aview A x = Some (ab, w) ->
    (exists b, rv m (wz (to_Z x)) = Some b /\ abyte_val ρ ab b)
    /\ (w = true -> wview segs m (wz (to_Z x)) <> None))
  /\ RWin ρ A m.

End WithSegs.

Section Reads.
Variable segs : list Segment.

Fixpoint find_region (A : list region) (x : int) (n : int) : option region :=
  match A with
  | [] => None
  | R :: A' => if (rg_lo R <=? x)%uint63 && (x + n <=? rg_hi R)%uint63 && negb (is_win (rg_kind R)) then Some R else find_region A' x n
  end.

Fixpoint rbytes (R : region) (x : int) (n : nat) : list abyte :=
  match n with
  | O => []
  | S n' => rbyte segs R x :: rbytes R (x + 1)%uint63 n'
  end.

Definition rbytes_fast (R : region) (x : int) (n : nat) : list abyte :=
  let o := cell_off R x in
  if Nat.leb (o + n) 8 then (let c := get_cell segs R (cell_key R x) in map (fun i => cbyte c (o + i)) (seq 0 n))
  else rbytes R x n.

Definition a_bytes (A : list region) (x : int) (n : nat) : option (list abyte * bool) :=
  match find_region A x (of_Z (Z.of_nat n)) with
  | Some R => Some (rbytes_fast R x n, rk_writable (rg_kind R))
  | None => None
  end.

End Reads.

Section ReadLemmas.
Variable segs : list Segment.

End ReadLemmas.

Section LoadStore.
Variable segs : list Segment.

End LoadStore.

Section Stores.
Variable segs : list Segment.

Definition cell_write (c : cell) (o : nat) (nb : list abyte) : cell :=
  CB (map (fun j => if Nat.leb o j && Nat.ltb j (o + length nb) then nth (j - o) nb BT else cbyte c j) (seq 0 8)).

Definition reg_with_cells (R : region) (t : itrie cell) : region :=
  Rg (rg_lo R) (rg_hi R) (rg_kind R) (rg_d R) t.

Definition rwrite (R : region) (x : int) (nb : list abyte) : region :=
  let k := cell_key R x in
  reg_with_cells R (iset (rg_d R) (rg_cells R) k (cell_write (get_cell segs R k) (cell_off R x) nb)).

Fixpoint rwrite_each (R : region) (x : int) (nb : list abyte) : region :=
  match nb with
  | [] => R
  | b :: nb' => rwrite_each (rwrite R x [b]) (x + 1)%uint63 nb'
  end.

Definition rwrite_all (R : region) (x : int) (nb : list abyte) : region :=
  if Nat.leb (cell_off R x + length nb) 8 then rwrite R x nb else rwrite_each R x nb.

Fixpoint replace_nth (A : list region) (i : nat) (R' : region) : list region :=
  match A, i with
  | [], _ => []
  | _ :: A', O => R' :: A'
  | R0 :: A', S i' => R0 :: replace_nth A' i' R'
  end.

Fixpoint find_region_i (A : list region) (x n : int) (i : nat) : option (nat * region) :=
  match A with
  | [] => None
  | R :: A' => if (rg_lo R <=? x)%uint63 && (x + n <=? rg_hi R)%uint63 && negb (is_win (rg_kind R)) then Some (i, R) else find_region_i A' x n (S i)
  end.

Definition a_store (A : list region) (x : int) (nb : list abyte) : option (list region) :=
  match find_region_i A x (of_Z (Z.of_nat (length nb))) 0 with
  | Some (i, R) => if rk_writable (rg_kind R) then Some (replace_nth A i (rwrite_all R x nb)) else None
  | None => None
  end.

End Stores.

Section StoreLemmas.
Variable segs : list Segment.

End StoreLemmas.

Section StoreSound.
Variable segs : list Segment.

End StoreSound.

Section MemFacts.
Variable segs : list Segment.

End MemFacts.
