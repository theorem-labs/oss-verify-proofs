(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ea0DefsK Ea0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Definition ART_LITW : list (Z * nat * Z) :=
  [
    (1303448 + 40, 4%nat, 0xffffffff); (1303448 + 56, 1%nat, 0); (0x10428, 8%nat, 0xafffff00000fffff); (0x139198, 8%nat, 0x1d14a0); (0x1d14a0, 8%nat, 4096);
    (0x1d3528 + 260, 1%nat, 0); (0x1d3528 + 144, 8%nat, 0);

    (0x1391b8, 8%nat, 0x1419f8); (0x1419f8, 8%nat, 0x7fff8000); (0x1391c0, 8%nat, 0x1426e8); (0x1426e8, 8%nat, 0); (0x1391c8, 8%nat, 0x1426f0); (0x1426f0, 8%nat, 0);
    (0x1391d0, 8%nat, 0x1426e0); (0x1426e0, 8%nat, 2 ^ 47 - 1); (0x1391b0, 8%nat, 0x13f1f8); (0x13f1f8 + 78, 1%nat, 1); (0x1391d8, 8%nat, 0x13b1c8); (0x13b1c8, 8%nat, 0x12b88c);
    (0x1391a8, 8%nat, 0x1d3528); (0x1d3528 + 120, 8%nat, 18446744073709551615); (0x14125c, 1%nat, 1);

    (0x141260, 1%nat, 1); (0x141264, 4%nat, 0); (0x675a80 - 88, 8%nat, 0x696f38);

    (0x10448, 8%nat, 0x218a392cd3d5dbf); (0x104c4, 1%nat, 3); (0x10370, 8%nat, 0xcc6e96b9cc6e96b9); (0x105c8, 1%nat, 4); (0x105f1, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x10420, 8%nat, 0x9747b28c9747b28c);

    (0x1426d8, 1%nat, 1); (0x1c3c62, 1%nat, 0); (1303448 + 3616, 8%nat, 2 ^ 40); (1303448 + 3624, 2%nat, 16); (1303448 + 3626, 2%nat, 2048);
    (0x1d34c0, 8%nat, 0); (0x1d34c8, 8%nat, 0); (0x13f1f8 + 44, 4%nat, 4096); (0x13f1f8 + 48, 4%nat, 0); (0x13f1f8 + 52, 4%nat, 190); (0x13f1f8 + 85, 1%nat, 1);
    (0x139e18, 8%nat, 0x10); (0x1426fc, 4%nat, 30); (0x1d3528 + 34, 1%nat, 1); (0x13e670 + 80, 8%nat, 2 ^ 20); (0x13e670 + 64, 8%nat, 2 ^ 28);

    (0x13b170, 8%nat, 0x12bfac); (0x13b000, 8%nat, 0x12b38c);

    (0x13b050, 8%nat, 0x128fa0); (0x13b008, 8%nat, 0x11dfec);

    (0x675a80 + 0x10, 4%nat, 0);

    (1303448 + 64, 8%nat, 4096); (1303448 + 64 + 56, 8%nat, 0); (1303448 + 64 + 48, 8%nat, 0); (1303448 + 64 + 616, 1%nat, 0);

    (0x13e670 + 160, 8%nat, 0); (0x13e670 + 168, 8%nat, 0); (0x13e670 + 176, 8%nat, 0); (0x13e670 + 184, 8%nat, 0); (0x13e670 + 152, 1%nat, 0); (0x13e670 + 153, 1%nat, 0);

    (0x1d1488, 1%nat, 0); (0x1d1489, 1%nat, 0);

    (0x6238d8, 4%nat, 1);

    (1303448 + 64 + 617, 3%nat, 0); (0x13e670 + 154, 2%nat, 0); (0x1d1488, 4%nat, 0);
    (0x1391a0, 8%nat, 0x13b200); (0x13b200, 8%nat, 0x1a607); (0x1426d9, 1%nat, 1); (0x1d3623, 1%nat, 1); (0x1d35b1, 1%nat, 1); (0x1d3528 + 84, 1%nat, 1);
    (0x1d1498, 4%nat, 0); (0x141a00, 4%nat, 1); (0x13b1c0, 8%nat, 0x12b488);

    (0x13e670 + 72, 8%nat, 0xe666661);
    (0x1391f8, 8%nat, 1);
    (0x13b158, 8%nat, 0x112324); (0x139d20, 8%nat, 0x1426d9); (0x13b0b8, 8%nat, 0x12c46c); (0x139208, 8%nat, 0x1d1498); (0x139fc0, 8%nat, 8);
    (0x1d357c, 1%nat, 1); (0x13b010, 8%nat, 0x131e8c); (0x13b018, 8%nat, 0x122888); (0x13b040, 8%nat, 0x128f84); (0x13b048, 8%nat, 0x122ca0);
    (0x13afc8, 8%nat, 0x13afc8); (0x13e340, 8%nat, 1); (0x13e390, 1%nat, 0); (0x13f210, 4%nat, 1); (0x13f2b0, 8%nat, 0); (0x1d38a0, 1%nat, 0);
    (0x675a78, 8%nat, 0x675aa0); (0x675aa8, 8%nat, 0x676280);

    (0x13afd0, 8%nat, 0x12bd70); (0x13b098, 8%nat, 0x11a034); (0x13b0a0, 8%nat, 0x12bcd8);

    (0x104c8, 1%nat, 4);

    (0x13f214, 1%nat, 0);

    (0x13b168, 8%nat, 0x11a21c);

    (0x13f258, 1%nat, 1);

    (0x13aff0, 8%nat, 0x12b458); (0x1d3626, 1%nat, 1); (0x1d3627, 1%nat, 1);

    (0x10390, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

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
