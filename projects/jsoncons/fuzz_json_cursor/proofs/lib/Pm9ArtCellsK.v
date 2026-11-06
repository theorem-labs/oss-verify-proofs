(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm9DefsK Pm9PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Definition ART_LITW : list (Z * nat * Z) :=
  [
    (1418904 + 40, 4%nat, 0xffffffff); (1418904 + 56, 1%nat, 0); (0x10458, 8%nat, 0xafffff00000fffff); (0x1544e0, 8%nat, 0x1ed7a0); (0x1ed7a0, 8%nat, 4096);
    (0x1ef828 + 260, 1%nat, 0); (0x1ef828 + 144, 8%nat, 0);

    (0x154500, 8%nat, 0x15dcf8); (0x15dcf8, 8%nat, 0x7fff8000); (0x154508, 8%nat, 0x15e9e8); (0x15e9e8, 8%nat, 0); (0x154510, 8%nat, 0x15e9f0); (0x15e9f0, 8%nat, 0);
    (0x154518, 8%nat, 0x15e9e0); (0x15e9e0, 8%nat, 2 ^ 47 - 1); (0x1544f8, 8%nat, 0x15b4f8); (0x15b4f8 + 78, 1%nat, 1); (0x154520, 8%nat, 0x156528); (0x156528, 8%nat, 0x1468c4);
    (0x1544f0, 8%nat, 0x1ef828); (0x1ef828 + 120, 8%nat, 18446744073709551615); (0x15d55c, 1%nat, 1);

    (0x15d560, 1%nat, 1); (0x15d564, 4%nat, 0); (0x691d90 - 88, 8%nat, 0x6b3248);

    (0x10478, 8%nat, 0x218a392cd3d5dbf); (0x104f4, 1%nat, 3); (0x10388, 8%nat, 0xcc6e96b9cc6e96b9); (0x105f8, 1%nat, 4); (0x10621, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10328, 8%nat, 0x35253c9ade8f4ca8); (0x10450, 8%nat, 0x9747b28c9747b28c);

    (0x15e9d8, 1%nat, 1); (0x1dff62, 1%nat, 0); (1418904 + 3616, 8%nat, 2 ^ 40); (1418904 + 3624, 2%nat, 16); (1418904 + 3626, 2%nat, 2048);
    (0x1ef7c0, 8%nat, 0); (0x1ef7c8, 8%nat, 0); (0x15b4f8 + 44, 4%nat, 4096); (0x15b4f8 + 48, 4%nat, 0); (0x15b4f8 + 52, 4%nat, 190); (0x15b4f8 + 85, 1%nat, 1);
    (0x155160, 8%nat, 0x10); (0x15e9fc, 4%nat, 30); (0x1ef828 + 34, 1%nat, 1); (0x15a970 + 80, 8%nat, 2 ^ 20); (0x15a970 + 64, 8%nat, 2 ^ 28);

    (0x1564d0, 8%nat, 0x146fe4); (0x156360, 8%nat, 0x1463c4);

    (0x691d90 + 0x10, 4%nat, 0);

    (1418904 + 64, 8%nat, 4096); (1418904 + 64 + 56, 8%nat, 0); (1418904 + 64 + 48, 8%nat, 0); (1418904 + 64 + 616, 1%nat, 0);

    (0x15a970 + 160, 8%nat, 0); (0x15a970 + 168, 8%nat, 0); (0x15a970 + 176, 8%nat, 0); (0x15a970 + 184, 8%nat, 0); (0x15a970 + 152, 1%nat, 0); (0x15a970 + 153, 1%nat, 0);

    (0x1ed788, 1%nat, 0); (0x1ed789, 1%nat, 0);

    (0x63fbd8, 4%nat, 1);

    (1418904 + 64 + 617, 3%nat, 0); (0x15a970 + 154, 2%nat, 0); (0x1ed788, 4%nat, 0);
    (0x1544e8, 8%nat, 0x156560); (0x156560, 8%nat, 0x1ada2); (0x15e9d9, 1%nat, 1); (0x1ef923, 1%nat, 1); (0x1ef8b1, 1%nat, 1); (0x1ef828 + 84, 1%nat, 1);
    (0x1ed798, 4%nat, 0); (0x15dd00, 4%nat, 1); (0x156520, 8%nat, 0x1464c0);

    (0x15a970 + 72, 8%nat, 0xe666661);
    (0x154540, 8%nat, 1);
    (0x1564b8, 8%nat, 0x12d2bc); (0x155068, 8%nat, 0x15e9d9); (0x156418, 8%nat, 0x1474a4); (0x154550, 8%nat, 0x1ed798); (0x155320, 8%nat, 8);
    (0x1ef87c, 1%nat, 1); (0x156370, 8%nat, 0x14cec4); (0x156378, 8%nat, 0x13d8c0); (0x1563a0, 8%nat, 0x143fbc); (0x1563a8, 8%nat, 0x13dcd8);
    (0x156328, 8%nat, 0x156328); (0x15a640, 8%nat, 1); (0x15a690, 1%nat, 0); (0x15b510, 4%nat, 1); (0x15b5b0, 8%nat, 0); (0x1efba0, 1%nat, 0);
    (0x691d88, 8%nat, 0x691db0); (0x691db8, 8%nat, 0x692590);

    (0x156330, 8%nat, 0x146da8); (0x1563f8, 8%nat, 0x134fcc); (0x156400, 8%nat, 0x146d10);

    (0x104f8, 1%nat, 4);

    (0x1564c8, 8%nat, 0x1351b4); (0x156350, 8%nat, 0x146490); (0x156358, 8%nat, 0x1463c0); (0x15b514, 1%nat, 0x0); (0x15b558, 1%nat, 0x1); (0x1ef926, 1%nat, 0x1); (0x1ef927, 1%nat, 0x1);

    (0x156368, 8%nat, 0x139024); (0x1563b0, 8%nat, 0x143fd8) ].

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
