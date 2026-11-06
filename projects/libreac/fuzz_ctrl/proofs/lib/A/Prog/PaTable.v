(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0b.v for libreac/fuzz_ctrl's program walk, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition A_TEXT : nat := 240.
Definition A_OBJ (i : nat) : nat := (241 + i)%nat.
Definition A_HI (j : nat) : nat := (280 + j)%nat.
Definition msize_eqb (a b : msize) : bool :=
match a, b with SZ1, SZ1 | SZ2, SZ2 | SZ4, SZ4 | SZ8, SZ8 => true | _, _ => false end.
Lemma msize_eqb_eq : forall a b, msize_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros H; try reflexivity; discriminate. Qed.
Lemma reg_eqb_eq : forall (a b : reg), bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Section c.
Variable psym : Type.
Inductive pinstr : Type :=
| PW (w : Z)
| PCall (s : psym) (rd : reg)
| PTail (s : psym)
| PHi (rd : reg) (j : nat)
| PAddHi (rd rs : reg) (j : nat) (a : nat) (off : Z)
| PLdHi (rd rs : reg) (j : nat) (a : nat) (off : Z) (sz : msize) (sg : bool).
Definition ptable := list pinstr.
Definition plookup_list (l : ptable) (k : Z) : option pinstr :=
if (k <? 0) || negb (k mod 4 =? 0) then None else nth_error l (Z.to_nat (k / 4)).
Section d.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Definition auipc_val (pc : Z) (imm : bv 20) : Z := zcanon (pc + bv_signed (bv_concat 32 imm (Z_to_bv 12 0))).
Definition pi_slot_check (k : Z) (e : pinstr) : bool :=
let pc := val A_TEXT + k in
match fetch pc with
| None => false
| Some wz =>
match e with
| PW w => Z.eqb wz w
| _ =>
match decode_any (Z_to_bv 32 wz) with
| Some (i, isz) =>
(isz =? 4) &&
match e, i with
| PCall s rd, Jal rd' imm => bv_eqb rd rd' && negb (bv_eqb rd' (Z_to_bv 5 0)) && (zcanon (pc + bv_signed imm) =? sigma s)
| PTail s, Jal rd' imm => bv_eqb rd' (Z_to_bv 5 0) && (zcanon (pc + bv_signed imm) =? sigma s)
| PHi rd j, Auipc rd' imm => bv_eqb rd rd' && (auipc_val pc imm =? val (A_HI j))
| PAddHi rd rs j a off, OpImm ALU_ADD rd' rs' imm =>
bv_eqb rd rd' && bv_eqb rs rs' && (val (A_HI j) + bv_signed imm =? val a + off)
| PLdHi rd rs j a off sz sg, Load sz' sg' rd' rs' imm =>
bv_eqb rd rd' && bv_eqb rs rs' && msize_eqb sz sz' && Bool.eqb sg sg' && (val (A_HI j) + bv_signed imm =? val a + off)
| _, _ => false
end
| None => false
end
end
end.
Fixpoint pi_check_from (k : Z) (l : list pinstr) : bool :=
match l with [] => true | e :: l' => pi_slot_check k e && pi_check_from (k + 4) l' end.
Definition pi_check (l : ptable) : bool := pi_check_from 0 l.
Lemma pi_check_from_slot : forall l k0 n e,
pi_check_from k0 l = true -> nth_error l n = Some e -> pi_slot_check (k0 + 4 * Z.of_nat n) e = true.
Proof.
induction l as [|x l IH]; intros k0 n e Hc Hn; [destruct n; discriminate|].
cbn in Hc. apply andb_prop in Hc as [Hx Hl].
destruct n as [|n]; cbn in Hn.
- injection Hn as <-. replace (k0 + 4 * Z.of_nat 0) with k0 by (cbn; rewrite Z.add_0_r; reflexivity). exact Hx.
- specialize (IH (k0 + 4) n e Hl Hn). replace (k0 + 4 * Z.of_nat (S n)) with (k0 + 4 + 4 * Z.of_nat n) by (rewrite Nat2Z.inj_succ; ring).
exact IH.
Qed.
Lemma pi_check_lookup : forall l k e,
pi_check l = true -> plookup_list l k = Some e -> pi_slot_check k e = true.
Proof.
intros l k e Hc Hl. unfold plookup_list in Hl.
destruct ((k <? 0) || negb (k mod 4 =? 0)) eqn:Hg; [discriminate|].
apply Bool.orb_false_elim in Hg as [Hneg Hmod]. apply Z.ltb_ge in Hneg. apply Bool.negb_false_iff in Hmod. apply Z.eqb_eq in Hmod.
pose proof (pi_check_from_slot l 0 (Z.to_nat (k / 4)) e Hc Hl) as H.
replace (0 + 4 * Z.of_nat (Z.to_nat (k / 4))) with k in H; [exact H|].
rewrite Z2Nat.id by (apply Z.div_pos; [exact Hneg|reflexivity]).
pose proof (Z.div_mod k 4 ltac:(discriminate)) as Hd. rewrite Hmod, Z.add_0_r in Hd. cbn. rewrite <- Hd. reflexivity.
Qed.
End d.
End c.
Arguments PW {psym} _.
Arguments PCall {psym} _ _.
Arguments PTail {psym} _.
Arguments PHi {psym} _ _.
Arguments PAddHi {psym} _ _ _ _ _.
Arguments PLdHi {psym} _ _ _ _ _ _ _.
