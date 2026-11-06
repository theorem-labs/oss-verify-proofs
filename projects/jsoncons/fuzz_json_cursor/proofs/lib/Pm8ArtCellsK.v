(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm8DefsK Pm8PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Definition ART_LITW : list (Z * nat * Z) :=
  [
    (1413976 + 40, 4%nat, 0xffffffff); (1413976 + 56, 1%nat, 0); (0x10440, 8%nat, 0xafffff00000fffff); (0x153118, 8%nat, 0x1ec460); (0x1ec460, 8%nat, 4096);
    (0x1ee4e8 + 260, 1%nat, 0); (0x1ee4e8 + 144, 8%nat, 0);

    (0x153138, 8%nat, 0x15c9b8); (0x15c9b8, 8%nat, 0x7fff8000); (0x153140, 8%nat, 0x15d6a8); (0x15d6a8, 8%nat, 0); (0x153148, 8%nat, 0x15d6b0); (0x15d6b0, 8%nat, 0);
    (0x153150, 8%nat, 0x15d6a0); (0x15d6a0, 8%nat, 2 ^ 47 - 1); (0x153130, 8%nat, 0x15a1b8); (0x15a1b8 + 78, 1%nat, 1); (0x153158, 8%nat, 0x155160); (0x155160, 8%nat, 0x145308);
    (0x153128, 8%nat, 0x1ee4e8); (0x1ee4e8 + 120, 8%nat, 18446744073709551615); (0x15c21c, 1%nat, 1);

    (0x15c220, 1%nat, 1); (0x15c224, 4%nat, 0); (0x690a50 - 88, 8%nat, 0x6b1f08);

    (0x10460, 8%nat, 0x218a392cd3d5dbf); (0x104dc, 1%nat, 3); (0x10378, 8%nat, 0xcc6e96b9cc6e96b9); (0x105e0, 1%nat, 4); (0x10609, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10328, 8%nat, 0x35253c9ade8f4ca8); (0x10438, 8%nat, 0x9747b28c9747b28c);

    (0x15d698, 1%nat, 1); (0x1dec22, 1%nat, 0); (1413976 + 3616, 8%nat, 2 ^ 40); (1413976 + 3624, 2%nat, 16); (1413976 + 3626, 2%nat, 2048);
    (0x1ee480, 8%nat, 0); (0x1ee488, 8%nat, 0); (0x15a1b8 + 44, 4%nat, 4096); (0x15a1b8 + 48, 4%nat, 0); (0x15a1b8 + 52, 4%nat, 190); (0x15a1b8 + 85, 1%nat, 1);
    (0x153d98, 8%nat, 0x10); (0x15d6bc, 4%nat, 30); (0x1ee4e8 + 34, 1%nat, 1); (0x159630 + 80, 8%nat, 2 ^ 20); (0x159630 + 64, 8%nat, 2 ^ 28);

    (0x155108, 8%nat, 0x145a28); (0x154f98, 8%nat, 0x144e08);

    (0x690a50 + 0x10, 4%nat, 0);

    (1413976 + 64, 8%nat, 4096); (1413976 + 64 + 56, 8%nat, 0); (1413976 + 64 + 48, 8%nat, 0); (1413976 + 64 + 616, 1%nat, 0);

    (0x159630 + 160, 8%nat, 0); (0x159630 + 168, 8%nat, 0); (0x159630 + 176, 8%nat, 0); (0x159630 + 184, 8%nat, 0); (0x159630 + 152, 1%nat, 0); (0x159630 + 153, 1%nat, 0);

    (0x1ec448, 1%nat, 0); (0x1ec449, 1%nat, 0);

    (0x63e898, 4%nat, 1);

    (1413976 + 64 + 617, 3%nat, 0); (0x159630 + 154, 2%nat, 0); (0x1ec448, 4%nat, 0);
    (0x153120, 8%nat, 0x155198); (0x155198, 8%nat, 0x1aa14); (0x15d699, 1%nat, 1); (0x1ee5e3, 1%nat, 1); (0x1ee571, 1%nat, 1); (0x1ee4e8 + 84, 1%nat, 1);
    (0x1ec458, 4%nat, 0); (0x15c9c0, 4%nat, 1); (0x155158, 8%nat, 0x144f04);

    (0x159630 + 72, 8%nat, 0xe666661);
    (0x153178, 8%nat, 1);
    (0x1550f0, 8%nat, 0x12bda0); (0x153ca0, 8%nat, 0x15d699); (0x155050, 8%nat, 0x145ee8); (0x153188, 8%nat, 0x1ec458); (0x153f58, 8%nat, 8);
    (0x1ee53c, 1%nat, 1); (0x154fa8, 8%nat, 0x14b908); (0x154fb0, 8%nat, 0x13c304); (0x154fd8, 8%nat, 0x142a00); (0x154fe0, 8%nat, 0x13c71c);
    (0x154f60, 8%nat, 0x154f60); (0x159300, 8%nat, 1); (0x159350, 1%nat, 0); (0x15a1d0, 4%nat, 1); (0x15a270, 8%nat, 0); (0x1ee860, 1%nat, 0);
    (0x690a48, 8%nat, 0x690a70); (0x690a78, 8%nat, 0x691250);

    (0x154f68, 8%nat, 0x1457ec); (0x155030, 8%nat, 0x133ab0); (0x155038, 8%nat, 0x145754);

    (0x104e0, 1%nat, 4);

    (0x155100, 8%nat, 0x133c98); (0x154f88, 8%nat, 0x144ed4); (0x154f90, 8%nat, 0x144e04); (0x15a1d4, 1%nat, 0x0); (0x15a218, 1%nat, 0x1); (0x1ee5e6, 1%nat, 0x1); (0x1ee5e7, 1%nat, 0x1);

    (0x154fa0, 8%nat, 0x137a68); (0x154fe8, 8%nat, 0x142a1c) ].

Definition chk_lit1 (k : list kentry) (c : Z * nat * Z) : bool :=
  let '(a, w, v) := c in
  (chk_sub k a w v || chk_img ASEGS0 ASAN0 k a w v || (chk_zero k (ELit 0) a (Z.of_nat w) && Z.eqb v 0 && Nat.leb w 8 && Z.leb 0 a))%bool.
Definition art_lits_chk (cs : acs) : bool := forallb (chk_lit1 (kn cs)) ART_LITW.

Section Lits.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Lemma art_lit1 : forall E cs R FULL model c, CSOK E cs R FULL model -> chk_lit1 (kn cs) c = true ->
    cell ASEGS0 FULL (fst (fst c)) (snd (fst c)) (snd c).
  Proof.
    intros E cs R FULL model [[a w] v] HC H. cbn [fst snd]. unfold chk_lit1 in H. unfold cell.
    apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
    - exact (hc_sub ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model a w v HC H).
    - exact (hc_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model a w v HC H).
    - apply andb_prop in H as [H Ha]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hv].
      apply Z.eqb_eq in Hv. subst v. apply Nat.leb_le in Hw. apply Z.leb_le in Ha.
      apply (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (ELit 0) a (Z.of_nat w) HC H a w Hw);
        unfold uE; cbn [edenot]; rewrite u64_lit by lia; lia.
  Qed.

  Lemma art_lit : forall E cs R FULL model, CSOK E cs R FULL model -> art_lits_chk cs = true ->
    forall a w v, In (a, w, v) ART_LITW -> cell ASEGS0 FULL a w v.
  Proof.
    intros E cs R FULL model HC H a w v Hin.
    exact (art_lit1 E cs R FULL model (a, w, v) HC (proj1 (forallb_forall _ _) H _ Hin)).
  Qed.
End Lits.

Lemma cell0_cat : forall (M : word -> option byte) a (w1 w2 : nat), 0 <= a -> a + Z.of_nat w1 < 2 ^ 64 -> (w1 + w2 <= 8)%nat ->
  cell ASEGS0 M a w1 0 -> cell ASEGS0 M (a + Z.of_nat w1) w2 0 -> cell ASEGS0 M a (w1 + w2) 0.
Proof.
  intros M a w1 w2 Ha Hn Hw H1 H2. unfold cell in *. rewrite wleb_zero in * by lia.
  assert (H2' : rdn ASEGS0 M (Z_to_bv 64 a + nat_to_word w1)%bv w2 = Some (repeat (Z_to_bv 8 0) w2)).
  { replace (Z_to_bv 64 a + nat_to_word w1)%bv with (Z_to_bv 64 (a + Z.of_nat w1)); [exact H2|].
    apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (Z.of_nat w1)) by lia. reflexivity. }
  rewrite (rdn_app ASEGS0 M w1 w2 (Z_to_bv 64 a) _ _ H1 H2'). rewrite repeat_app. reflexivity.
Qed.
