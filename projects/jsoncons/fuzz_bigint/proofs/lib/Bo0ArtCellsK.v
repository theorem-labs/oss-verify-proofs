(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Bo0DefsK Bo0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (897240 + 40, 4%nat, 0xffffffff); (897240 + 56, 1%nat, 0); (0x103d8, 8%nat, 0xafffff00000fffff); (0xd64a8, 8%nat, 0x16e1e0); (0x16e1e0, 8%nat, 4096);
    (0x170268 + 260, 1%nat, 0); (0x170268 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0xd64c8, 8%nat, 0xde738); (0xde738, 8%nat, 0x7fff8000); (0xd64d0, 8%nat, 0xdf428); (0xdf428, 8%nat, 0); (0xd64d8, 8%nat, 0xdf430); (0xdf430, 8%nat, 0);
    (0xd64e0, 8%nat, 0xdf420); (0xdf420, 8%nat, 2 ^ 47 - 1); (0xd64c0, 8%nat, 0xdbf38); (0xdbf38 + 78, 1%nat, 1); (0xd64e8, 8%nat, 0xd8428); (0xd8428, 8%nat, 0xcc740);
    (0xd64b8, 8%nat, 0x170268); (0x170268 + 120, 8%nat, 18446744073709551615); (0xddf9c, 1%nat, 1);
    (* [comment removed for export] *)
    (0xddfa0, 1%nat, 1); (0xddfa4, 4%nat, 0); (0x611908 - 88, 8%nat, 0x632cb0);
    (* [comment removed for export] *)
    (0x103e8, 8%nat, 0x218a392cd3d5dbf); (0x1045c, 1%nat, 3); (0x10340, 8%nat, 0xcc6e96b9cc6e96b9); (0x10560, 1%nat, 4); (0x10589, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10310, 8%nat, 0x35253c9ade8f4ca8); (0x103d0, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0xdf418, 1%nat, 1); (0x1609a2, 1%nat, 0); (897240 + 3616, 8%nat, 2 ^ 40); (897240 + 3624, 2%nat, 16); (897240 + 3626, 2%nat, 2048);
    (0x170200, 8%nat, 0); (0x170208, 8%nat, 0); (0xdbf38 + 44, 4%nat, 4096); (0xdbf38 + 48, 4%nat, 0); (0xdbf38 + 52, 4%nat, 190); (0xdbf38 + 85, 1%nat, 1);
    (0xd7120, 8%nat, 0x10); (0xdf43c, 4%nat, 30); (0x170268 + 34, 1%nat, 1); (0xdb3b0 + 80, 8%nat, 2 ^ 20); (0xdb3b0 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0xd83d0, 8%nat, 0xccc60); (0xd82c8, 8%nat, 0xcc240);
    (* [comment removed for export] *)
    (0x611908 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (897240 + 64, 8%nat, 4096); (897240 + 64 + 56, 8%nat, 0); (897240 + 64 + 48, 8%nat, 0); (897240 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0xdb3b0 + 160, 8%nat, 0); (0xdb3b0 + 168, 8%nat, 0); (0xdb3b0 + 176, 8%nat, 0); (0xdb3b0 + 184, 8%nat, 0); (0xdb3b0 + 152, 1%nat, 0); (0xdb3b0 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x16e1c8, 1%nat, 0); (0x16e1c9, 1%nat, 0);
    (* [comment removed for export] *)
    (0x5c0618, 4%nat, 1);
    (* [comment removed for export] *)
    (897240 + 64 + 617, 3%nat, 0); (0xdb3b0 + 154, 2%nat, 0); (0x16e1c8, 4%nat, 0);
    (0xd64b0, 8%nat, 0xd8460); (0xd8460, 8%nat, 0x1a149); (0xdf419, 1%nat, 1); (0x170363, 1%nat, 1); (0x1702f1, 1%nat, 1); (0x170268 + 84, 1%nat, 1);
    (0x16e1d8, 4%nat, 0); (0xde740, 4%nat, 1); (0xd8420, 8%nat, 0xcc33c);
    (* [comment removed for export] *)
    (0xdb3b0 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0xd6508, 8%nat, 1);
    (0xd83c8, 8%nat, 0xb6514); (0xd7030, 8%nat, 0xdf419); (0xd8348, 8%nat, 0xcd0b0); (0xd6518, 8%nat, 0x16e1d8); (0xd7290, 8%nat, 8);
    (0x1702bc, 1%nat, 1); (0xd82d8, 8%nat, 0xd1bc0); (0xd82e0, 8%nat, 0xc44f0); (0xd82f8, 8%nat, 0xc9fd8); (0xd8300, 8%nat, 0xc484c);
    (0xd8298, 8%nat, 0xd8298); (0xdb080, 8%nat, 1); (0xdb0d0, 1%nat, 0); (0xdbf50, 4%nat, 1); (0xdbff0, 8%nat, 0); (0x1705e0, 1%nat, 0);
    (0x611900, 8%nat, 0x611928); (0x611930, 8%nat, 0x612108);
    (* [comment removed for export] *)
    (0xd82a0, 8%nat, 0xcca24); (0xd8328, 8%nat, 0xbdd78); (0xd8330, 8%nat, 0xcc98c);
    (* [comment removed for export] *)
    (0x10460, 1%nat, 4) ].

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
