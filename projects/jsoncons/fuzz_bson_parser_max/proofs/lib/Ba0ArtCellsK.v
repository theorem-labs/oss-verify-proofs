(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ba0DefsK Ba0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1286488 + 40, 4%nat, 0xffffffff); (1286488 + 56, 1%nat, 0); (0x10418, 8%nat, 0xafffff00000fffff); (0x134fb8, 8%nat, 0x1cd260); (0x1cd260, 8%nat, 4096);
    (0x1cf2e8 + 260, 1%nat, 0); (0x1cf2e8 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x134fd8, 8%nat, 0x13d7b8); (0x13d7b8, 8%nat, 0x7fff8000); (0x134fe0, 8%nat, 0x13e4a8); (0x13e4a8, 8%nat, 0); (0x134fe8, 8%nat, 0x13e4b0); (0x13e4b0, 8%nat, 0);
    (0x134ff0, 8%nat, 0x13e4a0); (0x13e4a0, 8%nat, 2 ^ 47 - 1); (0x134fd0, 8%nat, 0x13afb8); (0x13afb8 + 78, 1%nat, 1); (0x134ff8, 8%nat, 0x136fe8); (0x136fe8, 8%nat, 0x127758);
    (0x134fc8, 8%nat, 0x1cf2e8); (0x1cf2e8 + 120, 8%nat, 18446744073709551615); (0x13d01c, 1%nat, 1);
    (* [comment removed for export] *)
    (0x13d020, 1%nat, 1); (0x13d024, 4%nat, 0); (0x671880 - 88, 8%nat, 0x692d38);
    (* [comment removed for export] *)
    (0x10430, 8%nat, 0x218a392cd3d5dbf); (0x104b4, 1%nat, 3); (0x10358, 8%nat, 0xcc6e96b9cc6e96b9); (0x105b8, 1%nat, 4); (0x105e1, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10320, 8%nat, 0x35253c9ade8f4ca8); (0x10410, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x13e498, 1%nat, 1); (0x1bfa22, 1%nat, 0); (1286488 + 3616, 8%nat, 2 ^ 40); (1286488 + 3624, 2%nat, 16); (1286488 + 3626, 2%nat, 2048);
    (0x1cf280, 8%nat, 0); (0x1cf288, 8%nat, 0); (0x13afb8 + 44, 4%nat, 4096); (0x13afb8 + 48, 4%nat, 0); (0x13afb8 + 52, 4%nat, 190); (0x13afb8 + 85, 1%nat, 1);
    (0x135c38, 8%nat, 0x10); (0x13e4bc, 4%nat, 30); (0x1cf2e8 + 34, 1%nat, 1); (0x13a430 + 80, 8%nat, 2 ^ 20); (0x13a430 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x136f90, 8%nat, 0x127e78); (0x136e20, 8%nat, 0x127258);
    (* [comment removed for export] *)
    (0x671880 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1286488 + 64, 8%nat, 4096); (1286488 + 64 + 56, 8%nat, 0); (1286488 + 64 + 48, 8%nat, 0); (1286488 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x13a430 + 160, 8%nat, 0); (0x13a430 + 168, 8%nat, 0); (0x13a430 + 176, 8%nat, 0); (0x13a430 + 184, 8%nat, 0); (0x13a430 + 152, 1%nat, 0); (0x13a430 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1cd248, 1%nat, 0); (0x1cd249, 1%nat, 0);
    (* [comment removed for export] *)
    (0x61f698, 4%nat, 1);
    (* [comment removed for export] *)
    (1286488 + 64 + 617, 3%nat, 0); (0x13a430 + 154, 2%nat, 0); (0x1cd248, 4%nat, 0);
    (0x134fc0, 8%nat, 0x137020); (0x137020, 8%nat, 0x1a615); (0x13e499, 1%nat, 1); (0x1cf3e3, 1%nat, 1); (0x1cf371, 1%nat, 1); (0x1cf2e8 + 84, 1%nat, 1);
    (0x1cd258, 4%nat, 0); (0x13d7c0, 4%nat, 1); (0x136fe0, 8%nat, 0x127354);
    (* [comment removed for export] *)
    (0x13a430 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x135018, 8%nat, 1);
    (0x136f78, 8%nat, 0x10e1f4); (0x135b40, 8%nat, 0x13e499); (0x136ed8, 8%nat, 0x128338); (0x135028, 8%nat, 0x1cd258); (0x135de0, 8%nat, 8);
    (0x1cf33c, 1%nat, 1); (0x136e30, 8%nat, 0x12dd58); (0x136e38, 8%nat, 0x11e754); (0x136e60, 8%nat, 0x124e50); (0x136e68, 8%nat, 0x11eb6c);
    (0x136de8, 8%nat, 0x136de8); (0x13a100, 8%nat, 1); (0x13a150, 1%nat, 0); (0x13afd0, 4%nat, 1); (0x13b070, 8%nat, 0); (0x1cf660, 1%nat, 0);
    (0x671878, 8%nat, 0x6718a0); (0x6718a8, 8%nat, 0x672080);
    (* [comment removed for export] *)
    (0x136df0, 8%nat, 0x127c3c); (0x136eb8, 8%nat, 0x115f04); (0x136ec0, 8%nat, 0x127ba4);
    (* [comment removed for export] *)
    (0x104b8, 1%nat, 4);
    (* [comment removed for export] *)
    (0x13afd4, 1%nat, 0);
    (* [comment removed for export] *)
    (0x136f88, 8%nat, 0x1160ec);
    (* [comment removed for export] *)
    (0x13b018, 1%nat, 1);
    (* [comment removed for export] *)
    (0x136e10, 8%nat, 0x127324); (0x1cf3e6, 1%nat, 1); (0x1cf3e7, 1%nat, 1);
    (* [comment removed for export] *)
    (0x10378, 8%nat, 0xf5f5f5f5f5f5f5f5) ].

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
