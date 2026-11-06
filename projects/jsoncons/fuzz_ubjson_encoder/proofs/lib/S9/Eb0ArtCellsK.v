(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Eb0DefsK Eb0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Definition ART_LITW : list (Z * nat * Z) :=
  [
    (1321624 + 40, 4%nat, 0xffffffff); (1321624 + 56, 1%nat, 0); (0x10430, 8%nat, 0xafffff00000fffff); (0x13d8a8, 8%nat, 0x1d5ba0); (0x1d5ba0, 8%nat, 4096);
    (0x1d7c28 + 260, 1%nat, 0); (0x1d7c28 + 144, 8%nat, 0);

    (0x13d8c8, 8%nat, 0x1460f8); (0x1460f8, 8%nat, 0x7fff8000); (0x13d8d0, 8%nat, 0x146de8); (0x146de8, 8%nat, 0); (0x13d8d8, 8%nat, 0x146df0); (0x146df0, 8%nat, 0);
    (0x13d8e0, 8%nat, 0x146de0); (0x146de0, 8%nat, 2 ^ 47 - 1); (0x13d8c0, 8%nat, 0x1438f8); (0x1438f8 + 78, 1%nat, 1); (0x13d8e8, 8%nat, 0x13f8d8); (0x13f8d8, 8%nat, 0x130034);
    (0x13d8b8, 8%nat, 0x1d7c28); (0x1d7c28 + 120, 8%nat, 18446744073709551615); (0x14595c, 1%nat, 1);

    (0x145960, 1%nat, 1); (0x145964, 4%nat, 0); (0x67a180 - 88, 8%nat, 0x69b638);

    (0x10450, 8%nat, 0x218a392cd3d5dbf); (0x104cc, 1%nat, 3); (0x10378, 8%nat, 0xcc6e96b9cc6e96b9); (0x105d0, 1%nat, 4); (0x105f9, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x10428, 8%nat, 0x9747b28c9747b28c);

    (0x146dd8, 1%nat, 1); (0x1c8362, 1%nat, 0); (1321624 + 3616, 8%nat, 2 ^ 40); (1321624 + 3624, 2%nat, 16); (1321624 + 3626, 2%nat, 2048);
    (0x1d7bc0, 8%nat, 0); (0x1d7bc8, 8%nat, 0); (0x1438f8 + 44, 4%nat, 4096); (0x1438f8 + 48, 4%nat, 0); (0x1438f8 + 52, 4%nat, 190); (0x1438f8 + 85, 1%nat, 1);
    (0x13e528, 8%nat, 0x10); (0x146dfc, 4%nat, 30); (0x1d7c28 + 34, 1%nat, 1); (0x142d70 + 80, 8%nat, 2 ^ 20); (0x142d70 + 64, 8%nat, 2 ^ 28);

    (0x13f880, 8%nat, 0x130754); (0x13f710, 8%nat, 0x12fb34);

    (0x13f760, 8%nat, 0x12d748); (0x13f718, 8%nat, 0x122794);

    (0x67a180 + 0x10, 4%nat, 0);

    (1321624 + 64, 8%nat, 4096); (1321624 + 64 + 56, 8%nat, 0); (1321624 + 64 + 48, 8%nat, 0); (1321624 + 64 + 616, 1%nat, 0);

    (0x142d70 + 160, 8%nat, 0); (0x142d70 + 168, 8%nat, 0); (0x142d70 + 176, 8%nat, 0); (0x142d70 + 184, 8%nat, 0); (0x142d70 + 152, 1%nat, 0); (0x142d70 + 153, 1%nat, 0);

    (0x1d5b88, 1%nat, 0); (0x1d5b89, 1%nat, 0);

    (0x627fd8, 4%nat, 1);

    (1321624 + 64 + 617, 3%nat, 0); (0x142d70 + 154, 2%nat, 0); (0x1d5b88, 4%nat, 0);
    (0x13d8b0, 8%nat, 0x13f910); (0x13f910, 8%nat, 0x1a76e); (0x146dd9, 1%nat, 1); (0x1d7d23, 1%nat, 1); (0x1d7cb1, 1%nat, 1); (0x1d7c28 + 84, 1%nat, 1);
    (0x1d5b98, 4%nat, 0); (0x146100, 4%nat, 1); (0x13f8d0, 8%nat, 0x12fc30);

    (0x142d70 + 72, 8%nat, 0xe666661);
    (0x13d908, 8%nat, 1);
    (0x13f868, 8%nat, 0x116acc); (0x13e430, 8%nat, 0x146dd9); (0x13f7c8, 8%nat, 0x130c14); (0x13d918, 8%nat, 0x1d5b98); (0x13e6d0, 8%nat, 8);
    (0x1d7c7c, 1%nat, 1); (0x13f720, 8%nat, 0x136634); (0x13f728, 8%nat, 0x127030); (0x13f750, 8%nat, 0x12d72c); (0x13f758, 8%nat, 0x127448);
    (0x13f6d8, 8%nat, 0x13f6d8); (0x142a40, 8%nat, 1); (0x142a90, 1%nat, 0); (0x143910, 4%nat, 1); (0x1439b0, 8%nat, 0); (0x1d7fa0, 1%nat, 0);
    (0x67a178, 8%nat, 0x67a1a0); (0x67a1a8, 8%nat, 0x67a980);

    (0x13f6e0, 8%nat, 0x130518); (0x13f7a8, 8%nat, 0x11e7dc); (0x13f7b0, 8%nat, 0x130480);

    (0x104d0, 1%nat, 4);

    (0x143914, 1%nat, 0);

    (0x13f878, 8%nat, 0x11e9c4);

    (0x143958, 1%nat, 1);

    (0x13f700, 8%nat, 0x12fc00); (0x1d7d26, 1%nat, 1); (0x1d7d27, 1%nat, 1);

    (0x10398, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

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
