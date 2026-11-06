(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib U1CxxTable U1Statics.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition SX_BB : nat := 2.

Definition dsx_blobs : list (list byte) := map (fun r : run => map (Z_to_bv 8) (snd r)) D_RD.
Lemma dsx_blobs_eq : dsx_blobs = map (fun r : run => map (Z_to_bv 8) (snd r)) D_RD.
Proof. vm_compute. reflexivity. Qed.

Fixpoint kn_sx_of (rs : list run) (j : nat) : list kentry :=
  match rs with
  | [] => []
  | (a, bs) :: rest => KBlob (SA (ELit 0) a) (ELit (Z.of_nat (length bs))) j :: kn_sx_of rest (S j)
  end.
Definition kn_sx : list kentry := Eval vm_compute in kn_sx_of D_RD SX_BB.
Lemma kn_sx_eq : kn_sx = kn_sx_of D_RD SX_BB. Proof. vm_compute. reflexivity. Qed.

Definition runs_self_lookup (rs : list run) : bool :=
  forallb (fun r : run => forallb (fun i => ozeqb (lookup_byte rs (fst r + Z.of_nat i)) (Some (nth i (snd r) 0)))
                                  (seq 0 (length (snd r)))) rs.
Lemma D_RD_self : runs_self_lookup D_RD = true. Proof. vm_compute. reflexivity. Qed.

Definition kentry_eqb (a b : kentry) : bool :=
  match a, b with
  | KBlob (SA b1 k1) n1 j1, KBlob (SA b2 k2) n2 j2 => expr_eqb b1 b2 && Z.eqb k1 k2 && expr_eqb n1 n2 && Nat.eqb j1 j2
  | _, _ => false
  end.

Definition has_sx (kn : list kentry) : bool := forallb (fun K => existsb (kentry_eqb K) kn) kn_sx.

Section K.
  Variable E : env.
  Variable M : word -> option byte.

  Definition blobs_sx_ok : Prop := forall j, (j < length D_RD)%nat -> eb E (SX_BB + j)%nat = nth j dsx_blobs [].

  Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0. Proof. reflexivity. Qed.

  Lemma know_sx_of : forall rs j0,
    runs_within rs 0xef000 0x124000 = true ->
    (forall r i, In r rs -> (i < length (snd r))%nat -> M (Z_to_bv 64 (fst r + Z.of_nat i)) = Some (Z_to_bv 8 (nth i (snd r) 0))) ->
    (forall j r, nth_error rs j = Some r -> eb E (j0 + j)%nat = map (Z_to_bv 8) (snd r)) ->
    know_ok RSEGS E M (kn_sx_of rs j0).
  Proof.
    induction rs as [|[a bs] rest IH]; intros j0 Hok Hbytes Hbl; [constructor|].
    cbn [runs_within forallb fst snd] in Hok. apply andb_prop in Hok as [Hok Hrest]. apply andb_prop in Hok as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    cbn [kn_sx_of]. constructor.
    - cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite u0.
      rewrite (u_small (Z.of_nat (length bs))) by lia.
      pose proof (Hbl 0%nat (a, bs) eq_refl) as HB. rewrite Nat.add_0_r in HB. cbn [snd] in HB.
      split; [lia|]. split; [rewrite HB, length_map; lia|].
      intros i Hi. rewrite HB. rewrite Z.add_0_l. rewrite map_nth.
      replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
      apply (Hbytes (a, bs) (Z.to_nat i) (or_introl eq_refl)). cbn [snd]. lia.
    - apply (IH (S j0)); [exact Hrest| |].
      + intros r i Hr Hi. apply Hbytes; [right; exact Hr | exact Hi].
      + intros j r Hj. replace (S j0 + j)%nat with (j0 + S j)%nat by lia. apply (Hbl (S j)). exact Hj.
  Qed.

  Lemma self_bytes : forall rs, runs_self_lookup rs = true -> runs_within rs 0xef000 0x124000 = true -> pins rs M ->
    forall r i, In r rs -> (i < length (snd r))%nat -> M (Z_to_bv 64 (fst r + Z.of_nat i)) = Some (Z_to_bv 8 (nth i (snd r) 0)).
  Proof.
    intros rs Hs Hw HP r i Hr Hi. unfold runs_self_lookup in Hs. rewrite forallb_forall in Hs.
    specialize (Hs r Hr). rewrite forallb_forall in Hs. specialize (Hs i ltac:(apply in_seq; lia)).
    apply ozeqb_eq in Hs.
    unfold runs_within in Hw. rewrite forallb_forall in Hw. specialize (Hw r Hr).
    apply andb_prop in Hw as [W0 W1]. apply Z.leb_le in W0. apply Z.leb_le in W1.
    apply HP; [lia | exact Hs].
  Qed.

  Theorem know_sx : blobs_sx_ok -> pins D_RD M -> know_ok RSEGS E M kn_sx.
  Proof.
    intros HB HP. rewrite kn_sx_eq. apply know_sx_of.
    - apply D_RD_within.
    - apply self_bytes; [apply D_RD_self | apply D_RD_within | exact HP].
    - intros j r Hj.
      assert (Hjl : (j < length D_RD)%nat) by (apply (proj1 (nth_error_Some D_RD j)); rewrite Hj; discriminate).
      rewrite HB by exact Hjl. rewrite dsx_blobs_eq.
      apply (nth_error_nth _ _ []). apply (map_nth_error (fun r0 : run => map (Z_to_bv 8) (snd r0)) j D_RD Hj).
  Qed.

End K.

Lemma blobs_sx_ok_app : forall (vev : nat -> word) (l : list (list byte)),
  length l = SX_BB -> blobs_sx_ok (Env vev (blobs_ev (l ++ dsx_blobs))).
Proof.
  intros vev l Hl j Hj. cbn [eb]. unfold blobs_ev. rewrite app_nth2 by lia. rewrite Hl.
  replace (SX_BB + j - SX_BB)%nat with j by lia. reflexivity.
Qed.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb MemSplit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1Start U1CxxLink.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma main_entry_pins_sx : forall sp0 rdraw av ev uid hw tid regs mem,
  (0x7fff80000000 <= bv_unsigned sp0)%Z ->
  main_entry sp0 rdraw av ev uid hw tid regs mem -> pins D_RD mem.
Proof.
  intros sp0 rdraw av ev uid hw tid regs mem Hsp ME.
  destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & HJ & ->).
  intros y b Hy Hl. unfold cmem.
  pose proof (D_main1_pins sp0 av ev hw tid rdraw y b Hy Hl) as P.
  assert (Hylt : (y < 0x124000)%Z).
  {
    destruct (Z.lt_ge_cases y 0x124000) as [L|G]; [exact L|]. exfalso.
    assert (lookup_byte D_RD y = None); [|congruence].
    apply lookup_byte_none. intros Hin. unfold covered in Hin. apply in_flat_map in Hin as ([ra bs] & Hr & Hm).
    apply in_map_iff in Hm as (i & Hi1 & Hi). apply in_seq in Hi. cbn [fst snd] in Hi1.
    pose proof D_RD_within as WW. unfold runs_within in WW. rewrite forallb_forall in WW.
    specialize (WW _ Hr). cbn [fst snd] in WW, Hi. apply andb_prop in WW as [_ WW]. apply Z.leb_le in WW. lia. }
  rewrite (u_small y) by lia. unfold win_lo. rewrite stack_max_size_val.
  destruct (Z.leb_spec (bv_unsigned sp0) y); [lia|]. destruct (Z.leb_spec (bv_unsigned sp0 - 8388608) y); [lia|]. exact P.
Qed.
