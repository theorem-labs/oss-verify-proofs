(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ABytes ALayout FsKit AFake_iface ARepInit_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

Section CANSEC2. Context {rc : runConstT}.
Theorem afake_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok bsegs V m) asan_mem_facts ->
  Forall (pfact_ok V) asan_pure_facts ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->      (* [comment removed for export] *)
  AFAKE (mkALayout (LV V) w U) [] m.
Proof.
  intros V w U m HM HP HAT.
  set (L := mkALayout (LV V) w U).
  assert (EF : al_fake L = 4096 * V 377%nat) by reflexivity.
  assert (ED : al_dtls L = 4096 * V 310%nat) by reflexivity.
  assert (ET : al_t L = 4096 * V 227%nat) by reflexivity.
  pf V HP (PVar 377 1551 34359733495) P393. pf V HP (PVar 310 1 34359736319) P310. pf V HP (PVar 227 1 34359736319) P227.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512) DB393.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6287360) DI310.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6287360) DI227.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D3.
  mf V m HM (MCell (ZLit 6214280) 8 (ZLit 6214320)) C40.
  mf V m HM (MCell (ZLit 6214288) 8 (ZMul (ZLit 4096) (ZV 377))) C48.
  mf V m HM (MCell (ZLit 6214296) 8 (ZMul (ZLit 4096) (ZV 310))) C70.
  mf V m HM (MCell (ZLit 6214328) 8 (ZLit 6216336)) C98.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6214288)) CD24.
  mf V m HM (MCell (ZLit 1359536) 8 (ZLit 256)) CCF.
  mf V m HM (MCell (ZLit 1351064) 4 (ZLit 0)) CVERB.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6216136)) CT48.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6216356)) CT56.
  mf V m HM (MZeroC (ZMul (ZLit 4096) (ZV 377)) 88) HINTS.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 88)) 8 (ZLit 20)) CLOG.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 96)) 11571104) Z96.
  pose proof (mwr_find bsegs V m _ (ZMul (ZLit 4096) (ZV 377)) 11571200 HM ltac:(vm_compute; reflexivity)) as WFK. cbn [zv] in WFK.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400) ZSH.
  pose proof (mwr_find bsegs V m _ (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 HM ltac:(vm_compute; reflexivity)) as WSH. cbn [zv] in WSH.
  pose proof (mimg_cover bsegs V m _ 0x10000 0xb3fe8 HM ltac:(vm_compute; reflexivity)) as IMG.
  rewrite <- EF in *. rewrite <- ED in *. rewrite <- ET in *.
  assert (SHF : shad (al_fake L) = 512 * V 377%nat + 2147450880).
  { unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2, EF by lia. change (2^3) with 8.
    replace (4096 * V 377%nat) with ((512 * V 377%nat) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (SHL : shlen FAKESZ = 1446400) by reflexivity.
  assert (G : afake_geom L).
  { unfold afake_geom, FAKESZ, ablk, sclr, iclr, KLS, AIMG_LO, AIMG_HI. rewrite EF, ED, ET in *.
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ rewrite Z.mul_comm; apply Z_mod_mult
            | clear - P393 P0 P6 P10 DW393 DB393 HAT; lia
            | clear - P310 P0 P6 P10 DW310 DB310 DI310 HAT; lia
            | clear - P227 P0 P6 P10 DW227 DB227 DI227 HAT; lia
            | clear - D1 D2 D3; lia ]. }
  clearbody L.
  split; [exact G|].
  split.
  { unfold afake_cells. split.
    { eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xb3ee0 (le8 (Z_to_bv 64 0xac04c)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply IMG; rewrite length_le8 in Ha; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
    split; [apply (proj2 (rw_cells_app bsegs m 6214280 [C8 _] [C8 _])); split; [exact C40| cbn; exact C48]|].
    split; [exact C70|]. split; [exact C98|]. split; [exact CD24|]. split.
    { assert (CF8 : rw_cells bsegs m 1359536 ([C1 (Z_to_bv 8 0)] ++ ([C1 (Z_to_bv 8 1)] ++ [CB 6 (repeat (Z_to_bv 8 0) 6)]))).
      { eapply rw_cells_recast; [exact CCF| cbn; repeat split; reflexivity| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. }
      apply (proj1 (rw_cells_app bsegs m _ _ _)) in CF8 as [_ CF8]. cbn [cells_size csize Nat.add Z.of_nat Z.add Pos.of_succ_nat] in CF8.
      apply (proj1 (rw_cells_app bsegs m _ _ _)) in CF8 as [CF8 _]. exact CF8. }
    split; [exact CVERB|].
    apply (dc_of_cells m (al_t L + 48) [C8 (Z_to_bv 64 6216136); C8 (Z_to_bv 64 6216356)]).
    apply (proj2 (rw_cells_app bsegs m _ [C8 _] [C8 _])). split; [exact CT48| cbn [cells_size csize Nat.add]].
    replace (al_t L + 48 + Z.of_nat 8) with (al_t L + 56) by lia. exact CT56. }
  split.
  {
    pose proof (dc_of_cells m _ _ HINTS) as D88. cbn [cells_size csize Nat.add] in D88. change (Z.of_nat (Z.to_nat 88)) with 88 in D88.
    destruct (dc_take m _ 88 8 D88 ltac:(lia)) as [D0 R0]. destruct (c8_of_dc m _ D0) as [h0 H0].
    destruct (dc_take m _ (88 - 8) 8 R0 ltac:(lia)) as [D1' R1]. destruct (c8_of_dc m _ D1') as [h1 H1].
    destruct (dc_take m _ (88 - 8 - 8) 8 R1 ltac:(lia)) as [D2' R2]. destruct (c8_of_dc m _ D2') as [h2 H2].
    destruct (dc_take m _ (88 - 8 - 8 - 8) 64 R2 ltac:(lia)) as [[hs HS] _]. change (Z.to_nat 64) with 64%nat in HS.
    exists h0, h1, h2, hs.
    apply (proj2 (rw_cells_app bsegs m _ [C8 h0] _)). split; [exact H0| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app bsegs m _ [C8 h1] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact H1| cbn [cells_size csize Nat.add]].
    apply (proj2 (rw_cells_app bsegs m _ [C8 h2] _)). split; [replace (al_fake L + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8) by lia; exact H2| cbn [cells_size csize Nat.add]].
    replace (al_fake L + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (al_fake L + 8 + 8 + 8) by lia. exact HS. }
  split; [exact CLOG|].
  split.
  { eapply rw_cells_recast; [apply (mzero_rw_cells bsegs m (al_fake L + 96) 1); [intros i Hi; apply Z96; lia| eapply wr_at_sub'; [exact WFK| lia| lia| lia]| lia]
      | cbn; split; [reflexivity| exact I] | reflexivity | reflexivity]. }
  split.
  { exists (zeros (FAKESZ - 4096)). apply mzero_rw_cells; [| eapply wr_at_sub'; [exact WFK| lia| lia| unfold FAKESZ; lia]| unfold FAKESZ; lia].
    intros i Hi. replace (al_fake L + 4096 + i) with (al_fake L + 96 + (4000 + i)) by lia. apply Z96. unfold FAKESZ in Hi. lia. }
  split.
  { rewrite SHF, SHL. exists (zeros 1446400). apply mzero_rw_cells; [exact ZSH| exact WSH| lia]. }
  split.
  - intros c pos b Hc Hp Hb NZ. exfalso. apply NZ. pose proof (fk_flag_range L c pos Hc Hp) as R.
    specialize (Z96 (fk_flag L c pos - (al_fake L + 96)) ltac:(lia)). replace (al_fake L + 96 + (fk_flag L c pos - (al_fake L + 96))) with (fk_flag L c pos) in Z96 by lia.
    congruence.
  - intros c F n Hin. destruct Hin.
Qed.
End CANSEC2.
