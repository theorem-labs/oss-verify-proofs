(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).

Definition hid (P : Prop) : Prop := P.

Definition nodp (dpriv : Z -> Prop) (a n : Z) : Prop := forall i, a <= i < a + n -> ~ dpriv i.

Lemma cell_agree : forall (M M' : word -> option byte) a (n : nat) v,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M' x = M x) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  cellA M a n v -> cellA M' a n v.
Proof.
  intros M M' a n v AG Ha Hn C. unfold cell in *. rewrite <- C.
  apply rdn_ext. rewrite art_u_lit by lia. lia.
  intros x Hx. rewrite art_u_lit in Hx by lia. apply AG. lia.
Qed.

Lemma art_layout_Wf : forall M a k b, 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  apart a (Z.of_nat k) 0x153040 0xe000 -> apart a (Z.of_nat k) 0x1ee4e8 256 ->
  art_layout M -> art_layout (Wf M a k b).
Proof.
  intros M a k b Ha Hk A1 A2 L. unfold art_layout in *. unfold apart in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?c ?m _ => apply cell_Wf_other; [lia|lia|lia|lia|unfold apart; cbn; lia| tauto] end.
Qed.

Lemma art_layout_agree : forall M M', (forall x : word, bv_unsigned x < 0x6b3000 -> M' x = M x) -> art_layout M -> art_layout M'.
Proof.
  intros M M' AG L. unfold art_layout in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.

Lemma art_layout_agree2 : forall M M', (forall x : word, 0x10000 <= bv_unsigned x < 0x6b3000 -> M' x = M x) -> art_layout M -> art_layout M'.
Proof.
  intros M M' AG L. unfold art_layout in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.

Lemma art_layout_agree3 : forall M M', (forall x : word, 0x10000 <= bv_unsigned x < 0x22e888 -> M' x = M x) -> art_layout M -> art_layout M'.
Proof.
  intros M M' AG L. unfold art_layout in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Definition art_depot_kept (r : reg) : Prop :=
  r = 2%bv \/ r = 3%bv \/ r = 4%bv \/ r = 8%bv \/ r = 9%bv \/ (18 <= bv_unsigned r <= 27).
Definition art_depot_spec (DInv : nat -> (word -> option byte) -> Prop) (DPre : (word -> option byte) -> Z -> Z -> Prop) (dpriv : Z -> Prop)
                          (DRo : (word -> option byte) -> Prop) (DK : Z) : Prop :=
  forall (k : nat) regs (M rom : word -> option byte) (raw : word) (sp trp szt : Z),
    getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 trp -> getr regs 11 = Z_to_bv 64 szt ->
    DK <= sp -> sp < 2 ^ 64 -> 0x6b3000 <= sp - DK -> wrA M (sp - DK) DK -> nodp dpriv (sp - DK) DK -> DInv (S k) M -> DPre M trp szt -> DRo M ->
    exists regs' M' id,
      msteps ASEGS (mkst regs (0xa11a4 : word) M rom) (mkst regs' raw M' rom)
      /\ getr regs' 10 = Z_to_bv 64 id /\ 0 <= id < 2 ^ 32
      /\ (forall r : reg, art_depot_kept r -> getr regs' r = getr regs r)
      /\ mem_grows M M'
      /\ (forall x : word, ~ dpriv (bv_unsigned x) -> ~ (sp - DK <= bv_unsigned x < sp) -> M' x = M x)
      /\ DInv k M'.

Definition art_depot_frame (DInv : nat -> (word -> option byte) -> Prop) (dpriv : Z -> Prop) : Prop :=
  forall k M M', DInv k M -> (forall x : word, dpriv (bv_unsigned x) -> M' x = M x) -> DInv k M'.
Definition art_dpre_frame (DPre : (word -> option byte) -> Z -> Z -> Prop) : Prop :=
  forall M M' trp szt, DPre M trp szt -> (forall x : word, trp <= bv_unsigned x < trp + 8 * szt -> M' x = M x) -> DPre M' trp szt.

Definition art_dro_frame (DRo : (word -> option byte) -> Prop) : Prop :=
  forall M M', DRo M -> (forall x : word, 0x10000 <= bv_unsigned x < 0x22e888 -> M' x = M x) -> DRo M'.
End FPX.

Tactic Notation "klia" ne_hyp_list(l) := clear - l; lia.

Ltac oside :=
  cbn; try unfold apart;
  first [ lia
        | match goal with H : apart _ _ _ _ |- _ => unfold apart in H; destruct H; lia end
        | match goal with H : hid (_ \/ _) |- _ => unfold hid in H; destruct H; lia end ].
Ltac ond := let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; cbn in Hi; match goal with H : nodp _ _ _ |- _ => apply H; lia end.

Ltac zagree :=
  repeat (first [ reflexivity
                | rewrite Wn_outside; [ | lia | lia | oside ]
                | rewrite Wf_outside; [ | lia | rewrite ?Z2Nat.id by lia; lia | rewrite ?Z2Nat.id by lia; oside ] ]).
