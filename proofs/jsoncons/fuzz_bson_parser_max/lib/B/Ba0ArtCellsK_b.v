(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1295832 + 40, 4%nat, 0xffffffff); (1295832 + 56, 1%nat, 0); (0x10420, 8%nat, 0xafffff00000fffff); (0x1374a0, 8%nat, 0x1cf6e0); (0x1cf6e0, 8%nat, 4096);
    (0x1d1768 + 260, 1%nat, 0); (0x1d1768 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x1374c0, 8%nat, 0x13fc38); (0x13fc38, 8%nat, 0x7fff8000); (0x1374c8, 8%nat, 0x140928); (0x140928, 8%nat, 0); (0x1374d0, 8%nat, 0x140930); (0x140930, 8%nat, 0);
    (0x1374d8, 8%nat, 0x140920); (0x140920, 8%nat, 2 ^ 47 - 1); (0x1374b8, 8%nat, 0x13d438); (0x13d438 + 78, 1%nat, 1); (0x1374e0, 8%nat, 0x1394d0); (0x1394d0, 8%nat, 0x129d04);
    (0x1374b0, 8%nat, 0x1d1768); (0x1d1768 + 120, 8%nat, 18446744073709551615); (0x13f49c, 1%nat, 1);
    (* [comment removed for export] *)
    (0x13f4a0, 1%nat, 1); (0x13f4a4, 4%nat, 0); (0x673d00 - 88, 8%nat, 0x6951b8);
    (* [comment removed for export] *)
    (0x10438, 8%nat, 0x218a392cd3d5dbf); (0x104bc, 1%nat, 3); (0x10360, 8%nat, 0xcc6e96b9cc6e96b9); (0x105c0, 1%nat, 4); (0x105e9, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x10418, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x140918, 1%nat, 1); (0x1c1ea2, 1%nat, 0); (1295832 + 3616, 8%nat, 2 ^ 40); (1295832 + 3624, 2%nat, 16); (1295832 + 3626, 2%nat, 2048);
    (0x1d1700, 8%nat, 0); (0x1d1708, 8%nat, 0); (0x13d438 + 44, 4%nat, 4096); (0x13d438 + 48, 4%nat, 0); (0x13d438 + 52, 4%nat, 190); (0x13d438 + 85, 1%nat, 1);
    (0x138120, 8%nat, 0x10); (0x14093c, 4%nat, 30); (0x1d1768 + 34, 1%nat, 1); (0x13c8b0 + 80, 8%nat, 2 ^ 20); (0x13c8b0 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x139478, 8%nat, 0x12a424); (0x139308, 8%nat, 0x129804);
    (* [comment removed for export] *)
    (0x673d00 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1295832 + 64, 8%nat, 4096); (1295832 + 64 + 56, 8%nat, 0); (1295832 + 64 + 48, 8%nat, 0); (1295832 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x13c8b0 + 160, 8%nat, 0); (0x13c8b0 + 168, 8%nat, 0); (0x13c8b0 + 176, 8%nat, 0); (0x13c8b0 + 184, 8%nat, 0); (0x13c8b0 + 152, 1%nat, 0); (0x13c8b0 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1cf6c8, 1%nat, 0); (0x1cf6c9, 1%nat, 0);
    (* [comment removed for export] *)
    (0x621b18, 4%nat, 1);
    (* [comment removed for export] *)
    (1295832 + 64 + 617, 3%nat, 0); (0x13c8b0 + 154, 2%nat, 0); (0x1cf6c8, 4%nat, 0);
    (0x1374a8, 8%nat, 0x139508); (0x139508, 8%nat, 0x1a476); (0x140919, 1%nat, 1); (0x1d1863, 1%nat, 1); (0x1d17f1, 1%nat, 1); (0x1d1768 + 84, 1%nat, 1);
    (0x1cf6d8, 4%nat, 0); (0x13fc40, 4%nat, 1); (0x1394c8, 8%nat, 0x129900);
    (* [comment removed for export] *)
    (0x13c8b0 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x137500, 8%nat, 1);
    (0x139460, 8%nat, 0x1107a0); (0x138028, 8%nat, 0x140919); (0x1393c0, 8%nat, 0x12a8e4); (0x137510, 8%nat, 0x1cf6d8); (0x1382c8, 8%nat, 8);
    (0x1d17bc, 1%nat, 1); (0x139318, 8%nat, 0x130304); (0x139320, 8%nat, 0x120d00); (0x139348, 8%nat, 0x1273fc); (0x139350, 8%nat, 0x121118);
    (0x1392d0, 8%nat, 0x1392d0); (0x13c580, 8%nat, 1); (0x13c5d0, 1%nat, 0); (0x13d450, 4%nat, 1); (0x13d4f0, 8%nat, 0); (0x1d1ae0, 1%nat, 0);
    (0x673cf8, 8%nat, 0x673d20); (0x673d28, 8%nat, 0x674500);
    (* [comment removed for export] *)
    (0x1392d8, 8%nat, 0x12a1e8); (0x1393a0, 8%nat, 0x1184b0); (0x1393a8, 8%nat, 0x12a150);
    (* [comment removed for export] *)
    (0x104c0, 1%nat, 4);
    (* [comment removed for export] *)
    (0x13d454, 1%nat, 0);
    (* [comment removed for export] *)
    (0x139470, 8%nat, 0x118698);
    (* [comment removed for export] *)
    (0x13d498, 1%nat, 1);
    (* [comment removed for export] *)
    (0x1392f8, 8%nat, 0x1298d0); (0x1d1866, 1%nat, 1); (0x1d1867, 1%nat, 1);
    (* [comment removed for export] *)
    (0x10380, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

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

(* [comment removed for export] *)
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
