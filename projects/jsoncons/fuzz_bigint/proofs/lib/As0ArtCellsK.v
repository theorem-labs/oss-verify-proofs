(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AgentLib AsanAcct AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK As0DefsK As0PlanImagesK HandoffBridgeK HandoffCellsK ArtMem SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ART_LITW : list (Z * nat * Z) :=
  [ (* [comment removed for export] *)
    (894168 + 40, 4%nat, 0xffffffff); (894168 + 56, 1%nat, 0); (0x103d8, 8%nat, 0xafffff00000fffff); (0xd5898, 8%nat, 0x16d5e0); (0x16d5e0, 8%nat, 4096);
    (0x16f668 + 260, 1%nat, 0); (0x16f668 + 144, 8%nat, 0);
    (* [comment removed for export] *)
    (0xd58b8, 8%nat, 0xddb38); (0xddb38, 8%nat, 0x7fff8000); (0xd58c0, 8%nat, 0xde828); (0xde828, 8%nat, 0); (0xd58c8, 8%nat, 0xde830); (0xde830, 8%nat, 0);
    (0xd58d0, 8%nat, 0xde820); (0xde820, 8%nat, 2 ^ 47 - 1); (0xd58b0, 8%nat, 0xdb338); (0xdb338 + 78, 1%nat, 1); (0xd58d8, 8%nat, 0xd7818); (0xd7818, 8%nat, 0xcbb2c);
    (0xd58a8, 8%nat, 0x16f668); (0x16f668 + 120, 8%nat, 18446744073709551615); (0xdd39c, 1%nat, 1);
    (* [comment removed for export] *)
    (0xdd3a0, 1%nat, 1); (0xdd3a4, 4%nat, 0); (0x610d08 - 88, 8%nat, 0x6320b0);
    (* [comment removed for export] *)
    (0x103e8, 8%nat, 0x218a392cd3d5dbf); (0x1045c, 1%nat, 3); (0x10340, 8%nat, 0xcc6e96b9cc6e96b9); (0x10560, 1%nat, 4); (0x10589, 1%nat, 11);
    (0x102e8, 8%nat, 0xc6a4a7935bd1e995); (0x10310, 8%nat, 0x35253c9ade8f4ca8); (0x103d0, 8%nat, 0x9747b28c9747b28c);
    (* [comment removed for export] *)
    (0xde818, 1%nat, 1); (0x15fda2, 1%nat, 0); (894168 + 3616, 8%nat, 2 ^ 40); (894168 + 3624, 2%nat, 16); (894168 + 3626, 2%nat, 2048);
    (0x16f600, 8%nat, 0); (0x16f608, 8%nat, 0); (0xdb338 + 44, 4%nat, 4096); (0xdb338 + 48, 4%nat, 0); (0xdb338 + 52, 4%nat, 190); (0xdb338 + 85, 1%nat, 1);
    (0xd6510, 8%nat, 0x10); (0xde83c, 4%nat, 30); (0x16f668 + 34, 1%nat, 1); (0xda7b0 + 80, 8%nat, 2 ^ 20); (0xda7b0 + 64, 8%nat, 2 ^ 28);
    (* [comment removed for export] *)
    (0xd77c0, 8%nat, 0xcc04c); (0xd76b8, 8%nat, 0xcb62c);
    (* [comment removed for export] *)
    (0x610d08 + 0x10, 4%nat, 0);
    (* [comment removed for export] *)
    (894168 + 64, 8%nat, 4096); (894168 + 64 + 56, 8%nat, 0); (894168 + 64 + 48, 8%nat, 0); (894168 + 64 + 616, 1%nat, 0);
    (* [comment removed for export] *)
    (0xda7b0 + 160, 8%nat, 0); (0xda7b0 + 168, 8%nat, 0); (0xda7b0 + 176, 8%nat, 0); (0xda7b0 + 184, 8%nat, 0); (0xda7b0 + 152, 1%nat, 0); (0xda7b0 + 153, 1%nat, 0);
    (* [comment removed for export] *)
    (0x16d5c8, 1%nat, 0); (0x16d5c9, 1%nat, 0);
    (* [comment removed for export] *)
    (0x5bfa18, 4%nat, 1);
    (* [comment removed for export] *)
    (894168 + 64 + 617, 3%nat, 0); (0xda7b0 + 154, 2%nat, 0); (0x16d5c8, 4%nat, 0);
    (0xd58a0, 8%nat, 0xd7850); (0xd7850, 8%nat, 0x1a14b); (0xde819, 1%nat, 1); (0x16f763, 1%nat, 1); (0x16f6f1, 1%nat, 1); (0x16f668 + 84, 1%nat, 1);
    (0x16d5d8, 4%nat, 0); (0xddb40, 4%nat, 1); (0xd7810, 8%nat, 0xcb728);
    (* [comment removed for export] *)
    (0xda7b0 + 72, 8%nat, 0xe666661);   (* [comment removed for export] *)
    (0xd58f8, 8%nat, 1);
    (0xd77b8, 8%nat, 0xb5900); (0xd6420, 8%nat, 0xde819); (0xd7738, 8%nat, 0xcc49c); (0xd5908, 8%nat, 0x16d5d8); (0xd6680, 8%nat, 8);
    (0x16f6bc, 1%nat, 1); (0xd76c8, 8%nat, 0xd0fac); (0xd76d0, 8%nat, 0xc38dc); (0xd76e8, 8%nat, 0xc93c4); (0xd76f0, 8%nat, 0xc3c38);
    (0xd7688, 8%nat, 0xd7688); (0xda480, 8%nat, 1); (0xda4d0, 1%nat, 0); (0xdb350, 4%nat, 1); (0xdb3f0, 8%nat, 0); (0x16f9e0, 1%nat, 0);
    (0x610d00, 8%nat, 0x610d28); (0x610d30, 8%nat, 0x611508);
    (* [comment removed for export] *)
    (0xd7690, 8%nat, 0xcbe10); (0xd7718, 8%nat, 0xbd164); (0xd7720, 8%nat, 0xcbd78);
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
