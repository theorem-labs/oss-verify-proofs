(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4DefsK Pm4PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (1468568 + 40, 4%nat, 0xffffffff); (1468568 + 56, 1%nat, 0); (0x10440, 8%nat, 0xafffff00000fffff); (0x160bf8, 8%nat, 0x1f99a0); (0x1f99a0, 8%nat, 4096);
    (0x1fba28 + 260, 1%nat, 0); (0x1fba28 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0x160c18, 8%nat, 0x169ef8); (0x169ef8, 8%nat, 0x7fff8000); (0x160c20, 8%nat, 0x16abe8); (0x16abe8, 8%nat, 0); (0x160c28, 8%nat, 0x16abf0); (0x16abf0, 8%nat, 0);
    (0x160c30, 8%nat, 0x16abe0); (0x16abe0, 8%nat, 2 ^ 47 - 1); (0x160c10, 8%nat, 0x1676f8); (0x1676f8 + 78, 1%nat, 1); (0x160c38, 8%nat, 0x162c50); (0x162c50, 8%nat, 0x152ea4);
    (0x160c08, 8%nat, 0x1fba28); (0x1fba28 + 120, 8%nat, 18446744073709551615); (0x16975c, 1%nat, 1);
    (* [comment removed for export] *)
    (0x169760, 1%nat, 1); (0x169764, 4%nat, 0); (0x69dfd0 - 88, 8%nat, 0x6bf488);
    (* [comment removed for export] *)
    (0x10460, 8%nat, 0x218a392cd3d5dbf); (0x104dc, 1%nat, 3); (0x10378, 8%nat, 0xcc6e96b9cc6e96b9); (0x105e0, 1%nat, 4); (0x10609, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10328, 8%nat, 0x35253c9ade8f4ca8); (0x10438, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0x16abd8, 1%nat, 1); (0x1ec162, 1%nat, 0); (1468568 + 3616, 8%nat, 2 ^ 40); (1468568 + 3624, 2%nat, 16); (1468568 + 3626, 2%nat, 2048);
    (0x1fb9c0, 8%nat, 0); (0x1fb9c8, 8%nat, 0); (0x1676f8 + 44, 4%nat, 4096); (0x1676f8 + 48, 4%nat, 0); (0x1676f8 + 52, 4%nat, 190); (0x1676f8 + 85, 1%nat, 1);
    (0x161878, 8%nat, 0x10); (0x16abfc, 4%nat, 30); (0x1fba28 + 34, 1%nat, 1); (0x166b70 + 80, 8%nat, 2 ^ 20); (0x166b70 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0x162bf8, 8%nat, 0x1535c4); (0x162a88, 8%nat, 0x1529a4);
    (* [comment removed for export] *)
    (0x69dfd0 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (1468568 + 64, 8%nat, 4096); (1468568 + 64 + 56, 8%nat, 0); (1468568 + 64 + 48, 8%nat, 0); (1468568 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0x166b70 + 160, 8%nat, 0); (0x166b70 + 168, 8%nat, 0); (0x166b70 + 176, 8%nat, 0); (0x166b70 + 184, 8%nat, 0); (0x166b70 + 152, 1%nat, 0); (0x166b70 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x1f9988, 1%nat, 0); (0x1f9989, 1%nat, 0);
    (* [comment removed for export] *)
    (0x64bdd8, 4%nat, 1);
    (* [comment removed for export] *)
    (1468568 + 64 + 617, 3%nat, 0); (0x166b70 + 154, 2%nat, 0); (0x1f9988, 4%nat, 0);
    (0x160c00, 8%nat, 0x162c88); (0x162c88, 8%nat, 0x1acdf); (0x16abd9, 1%nat, 1); (0x1fbb23, 1%nat, 1); (0x1fbab1, 1%nat, 1); (0x1fba28 + 84, 1%nat, 1);
    (0x1f9998, 4%nat, 0); (0x169f00, 4%nat, 1); (0x162c48, 8%nat, 0x152aa0);
    (* [comment removed for export] *)
    (0x166b70 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0x160c58, 8%nat, 1);
    (0x162be0, 8%nat, 0x13993c); (0x161780, 8%nat, 0x16abd9); (0x162b40, 8%nat, 0x153a84); (0x160c68, 8%nat, 0x1f9998); (0x161a48, 8%nat, 8);
    (0x1fba7c, 1%nat, 1); (0x162a98, 8%nat, 0x1594a4); (0x162aa0, 8%nat, 0x149ea0); (0x162ac8, 8%nat, 0x15059c); (0x162ad0, 8%nat, 0x14a2b8);
    (0x162a50, 8%nat, 0x162a50); (0x166840, 8%nat, 1); (0x166890, 1%nat, 0); (0x167710, 4%nat, 1); (0x1677b0, 8%nat, 0); (0x1fbda0, 1%nat, 0);
    (0x69dfc8, 8%nat, 0x69dff0); (0x69dff8, 8%nat, 0x69e7d0);
    (* [comment removed for export] *)
    (0x162a58, 8%nat, 0x153388); (0x162b20, 8%nat, 0x14164c); (0x162b28, 8%nat, 0x1532f0);
    (* [comment removed for export] *)
    (0x104e0, 1%nat, 4);
    (* [comment removed for export] *)
    (0x162bf0, 8%nat, 0x141834); (0x162a78, 8%nat, 0x152a70); (0x162a80, 8%nat, 0x1529a0); (0x167714, 1%nat, 0x0); (0x167758, 1%nat, 0x1); (0x1fbb26, 1%nat, 0x1); (0x1fbb27, 1%nat, 0x1);
    (* [comment removed for export] *)
    (0x162a90, 8%nat, 0x145604); (0x162ad8, 8%nat, 0x1505b8) ].

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
