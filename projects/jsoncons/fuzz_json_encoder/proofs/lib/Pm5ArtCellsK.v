(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm5DefsK Pm5PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1483096 + 40, 4%nat, 0xffffffff); (1483096 + 56, 1%nat, 0); (0x10458, 8%nat, 0xafffff00000fffff); (0x1644f8, 8%nat, 0x1fd260); (0x1fd260, 8%nat, 4096);
    (0x1ff2e8 + 260, 1%nat, 0); (0x1ff2e8 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x164518, 8%nat, 0x16d7b8); (0x16d7b8, 8%nat, 0x7fff8000); (0x164520, 8%nat, 0x16e4a8); (0x16e4a8, 8%nat, 0); (0x164528, 8%nat, 0x16e4b0); (0x16e4b0, 8%nat, 0);
    (0x164530, 8%nat, 0x16e4a0); (0x16e4a0, 8%nat, 2 ^ 47 - 1); (0x164510, 8%nat, 0x16afb8); (0x16afb8 + 78, 1%nat, 1); (0x164538, 8%nat, 0x166550); (0x166550, 8%nat, 0x1568bc);
    (0x164508, 8%nat, 0x1ff2e8); (0x1ff2e8 + 120, 8%nat, 18446744073709551615); (0x16d01c, 1%nat, 1);
    (* [comment removed for export] *)
    (0x16d020, 1%nat, 1); (0x16d024, 4%nat, 0); (0x6a1890 - 88, 8%nat, 0x6c2d48);
    (* [comment removed for export] *)
    (0x10478, 8%nat, 0x218a392cd3d5dbf); (0x104f4, 1%nat, 3); (0x10388, 8%nat, 0xcc6e96b9cc6e96b9); (0x105f8, 1%nat, 4); (0x10621, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10328, 8%nat, 0x35253c9ade8f4ca8); (0x10450, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x16e498, 1%nat, 1); (0x1efa22, 1%nat, 0); (1483096 + 3616, 8%nat, 2 ^ 40); (1483096 + 3624, 2%nat, 16); (1483096 + 3626, 2%nat, 2048);
    (0x1ff280, 8%nat, 0); (0x1ff288, 8%nat, 0); (0x16afb8 + 44, 4%nat, 4096); (0x16afb8 + 48, 4%nat, 0); (0x16afb8 + 52, 4%nat, 190); (0x16afb8 + 85, 1%nat, 1);
    (0x165178, 8%nat, 0x10); (0x16e4bc, 4%nat, 30); (0x1ff2e8 + 34, 1%nat, 1); (0x16a430 + 80, 8%nat, 2 ^ 20); (0x16a430 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x1664f8, 8%nat, 0x156fdc); (0x166388, 8%nat, 0x1563bc);
    (* [comment removed for export] *)
    (0x6a1890 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1483096 + 64, 8%nat, 4096); (1483096 + 64 + 56, 8%nat, 0); (1483096 + 64 + 48, 8%nat, 0); (1483096 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x16a430 + 160, 8%nat, 0); (0x16a430 + 168, 8%nat, 0); (0x16a430 + 176, 8%nat, 0); (0x16a430 + 184, 8%nat, 0); (0x16a430 + 152, 1%nat, 0); (0x16a430 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1fd248, 1%nat, 0); (0x1fd249, 1%nat, 0);
    (* [comment removed for export] *)
    (0x64f698, 4%nat, 1);
    (* [comment removed for export] *)
    (1483096 + 64 + 617, 3%nat, 0); (0x16a430 + 154, 2%nat, 0); (0x1fd248, 4%nat, 0);
    (0x164500, 8%nat, 0x166588); (0x166588, 8%nat, 0x1b15a); (0x16e499, 1%nat, 1); (0x1ff3e3, 1%nat, 1); (0x1ff371, 1%nat, 1); (0x1ff2e8 + 84, 1%nat, 1);
    (0x1fd258, 4%nat, 0); (0x16d7c0, 4%nat, 1); (0x166548, 8%nat, 0x1564b8);
    (* [comment removed for export] *)
    (0x16a430 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x164558, 8%nat, 1);
    (0x1664e0, 8%nat, 0x13d2b4); (0x165080, 8%nat, 0x16e499); (0x166440, 8%nat, 0x15749c); (0x164568, 8%nat, 0x1fd258); (0x165348, 8%nat, 8);
    (0x1ff33c, 1%nat, 1); (0x166398, 8%nat, 0x15cebc); (0x1663a0, 8%nat, 0x14d8b8); (0x1663c8, 8%nat, 0x153fb4); (0x1663d0, 8%nat, 0x14dcd0);
    (0x166350, 8%nat, 0x166350); (0x16a100, 8%nat, 1); (0x16a150, 1%nat, 0); (0x16afd0, 4%nat, 1); (0x16b070, 8%nat, 0); (0x1ff660, 1%nat, 0);
    (0x6a1888, 8%nat, 0x6a18b0); (0x6a18b8, 8%nat, 0x6a2090);
    (* [comment removed for export] *)
    (0x166358, 8%nat, 0x156da0); (0x166420, 8%nat, 0x144fc4); (0x166428, 8%nat, 0x156d08);
    (* [comment removed for export] *)
    (0x104f8, 1%nat, 4);
    (* [comment removed for export] *)
    (0x1664f0, 8%nat, 0x1451ac); (0x166378, 8%nat, 0x156488); (0x166380, 8%nat, 0x1563b8); (0x16afd4, 1%nat, 0x0); (0x16b018, 1%nat, 0x1); (0x1ff3e6, 1%nat, 0x1); (0x1ff3e7, 1%nat, 0x1);
    (* [comment removed for export] *)
    (0x166390, 8%nat, 0x14901c); (0x1663d8, 8%nat, 0x153fd0) ].

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
