(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_defs. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks HxaIface HxaHandoffImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.


Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma seg_rw_pthread : seg_rw_ok bsegs 12565944 1088 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zero_region_ok_d (rho : valuation) (t n : int) (d : nat) (m : word -> option byte) (A : Z) :
  rho t = A -> 0 <= A -> A + to_Z n < two63 -> to_Z n < 2 ^ 62 -> to_Z n <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  (forall i, 0 <= i < to_Z n -> mrd bsegs m (wa (A + i)) = Some z8) ->
  region_ok bsegs rho t (RG None n 0 false DZero d IEmpty) m.
Proof.
  intros Er Hpos Hhi H62 Hd1 Hd2 Hb. pose proof (to_Z_bounded n) as Bn.
  unfold region_ok, rbase. cbn [rg_abs rg_size rg_al rg_wr rg_d]. rewrite Er. change (to_Z 0%uint63) with 0.
  split; [split; [exact Hpos | right; reflexivity]|]. split; [exact Hhi|]. split; [exact H62|]. split; [exact Hd1|]. split; [exact Hd2|].
  split; [lia|]. split; [apply Z.mod_1_r|].
  intros i Hi. exists z8. split; [exact (Hb i Hi)|]. split; [|discriminate].
  unfold rg_kb, rd_cell. cbn [rg_d rg_cells rg_dflt]. rewrite iget_empty. cbn [dflt_cell cell_kb].
  change (to_Z 255%uint63) with 255. rewrite testbit_255 by (apply Z.mod_pos_bound; lia). cbn [kb_ok].
  change (wZ w_zero) with 0. rewrite byteZ_0. reflexivity.
Qed.

Section Handoff.
Variables (rho : valuation) (m : word -> option byte) (ri : int).
Hypothesis H_ri : ri = 0%uint63 \/ ri = 16%uint63.
Hypothesis MI : mem_inv bsegs m.
Hypothesis V_relro : forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
Hypothesis V_lib : forall a, in_ranges LIB_PRISTINE a -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
Hypothesis C_key : rw_cells bsegs m 12565944 [C8 (Z_to_bv 64 0x1c0a60)].
Hypothesis C_shb : ro_cells bsegs m 6961656 [C8 (Z_to_bv 64 SHB)].
Hypothesis C_uar : ro_cells bsegs m 6961664 [C4 (Z_to_bv 64 1)].
Hypothesis C_tsd : rw_cells bsegs m 12430840 [C8 (Z_to_bv 64 0xbfc1f8)].
Variable canary : word.
Hypothesis C_can : ro_cells bsegs m 12562064 [C8 canary].
Hypothesis Hcan : rho T_CANARY = bv_unsigned canary.
Hypothesis H_imgsh : region_ok bsegs rho T_IMGSH RG_IMGSH m.
Variables (lo sp0 : Z).
Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hrho2 : rho 2%uint63 = sp0 - to_Z ri - 262144.
Hypothesis Hrho3 : rho 3%uint63 = shad (sp0 - to_Z ri - 262144).
Hypothesis Hlo : lo <= sp0 - to_Z ri - 262144.
Hypothesis Hlo0 : 0x7fff00000000 <= lo.
Hypothesis Hsp47 : sp0 + 16 <= USTACK_TOP.
Hypothesis Hsp32 : sp0 mod 32 = to_Z ri.
Hypothesis Z_stk : forall i, 0 <= i < (262144 + to_Z ri) / 8 -> mrd bsegs m (wa (shad (sp0 - to_Z ri - 262144) + i)) = Some z8.

Definition rg4_ok := HxaHandoffImg.rg4_ok rho m MI.
Definition rg5_ok := HxaHandoffImg.rg5_ok rho m V_relro.
Definition rg6_ok := HxaHandoffImg.rg6_ok rho m V_lib.
Definition rg8_ok := HxaHandoffImg.rg8_ok rho m V_lib.
Definition rg11_ok := HxaHandoffImg.rg11_ok rho m V_lib.
Definition rg15_ok := HxaHandoffImg.rg15_ok rho m V_lib.

Lemma Hri01 : to_Z ri = 0 \/ to_Z ri = 16.
Proof. destruct H_ri as [-> | ->]; [left | right]; reflexivity. Qed.
Lemma sz2 : to_Z (STK + ri)%uint63 = 262144 + to_Z ri.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.
Lemma sz3 : to_Z ((STK + ri) >> 3)%uint63 = (262144 + to_Z ri) / 8.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.

Local Ltac lit_cells t rg G ks bs :=
  apply (literal_region_ok bsegs rho t rg m _ ks bs eq_refl);
  [ closed_side | | exact G | closed_side | | closed_side ].

Lemma rg7_ok : region_ok bsegs rho 7%uint63 rg_7 m.
Proof.
  assert (G : bytes_at bsegs m (to_Z 6961656%uint63) (le8 (Z_to_bv 64 SHB) ++ le4 (Z_to_bv 64 1))).
  { apply bytes_at_app. destruct C_shb as [_ B1]. destruct C_uar as [_ B2]. cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2.
    split; [exact B1 | rewrite length_le8; exact B2]. }
  lit_cells 7%uint63 rg_7 G (kbs_Z 8 SHB ++ kbs_Z 4 1) (le8 (Z_to_bv 64 SHB) ++ le4 (Z_to_bv 64 1)).
  - apply Forall2_app; apply kbs_Z_intro; unfold SHB; lia.
  - discriminate.
Qed.

Lemma rg9_ok : region_ok bsegs rho 9%uint63 rg_9 m.
Proof. unfold rg_9. apply (unknown_region_ok bsegs rho); [closed_side | exact (proj2 (seg_rw_ok_sound bsegs _ _ seg_rw_errno m))]. Qed.

Lemma rg10_ok : region_ok bsegs rho 10%uint63 rg_10 m.
Proof. unfold rg_10. apply (unknown_region_ok bsegs rho); [closed_side | exact (proj2 (seg_rw_ok_sound bsegs _ _ seg_rw_tsd_used m))]. Qed.

Lemma rg12_ok : region_ok bsegs rho 12%uint63 rg_12 m.
Proof.
  assert (G : bytes_at bsegs m (to_Z 12430840%uint63) (le8 (Z_to_bv 64 0xbfc1f8))).
  { destruct C_tsd as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. }
  lit_cells 12%uint63 rg_12 G (kbs_Z 8 0xbfc1f8) (le8 (Z_to_bv 64 0xbfc1f8)).
  - apply kbs_Z_intro; lia.
  - discriminate.
Qed.

Lemma rg13_ok : region_ok bsegs rho 13%uint63 rg_13 m.
Proof.
  assert (G : bytes_at bsegs m (to_Z 12562064%uint63) (le8 canary)).
  { destruct C_can as [_ B1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. }
  lit_cells 13%uint63 rg_13 G (kbs_ptr T_CANARY) (le8 canary).
  - pose proof (bv_unsigned_in_range 64 canary) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (kbs_ptr_intro rho T_CANARY (bv_unsigned canary) Hcan Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
  - discriminate.
Qed.

Lemma rg14_ok : region_ok bsegs rho 14%uint63 rg_14 m.
Proof.
  assert (G : bytes_at bsegs m (to_Z 12565944%uint63) (le8 (Z_to_bv 64 0x1c0a60) ++ Z_to_le_bytes 1080 0)).
  { apply bytes_at_app. destruct C_key as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. split; [exact B1|].
    rewrite length_le8. change (to_Z 12565944%uint63 + Z.of_nat 8) with 12565952.
    apply (view_bytes_at m _ 12565952 rom_pthread_zero); [lia | rewrite length_Z_to_le_bytes; lia|].
    intros a Ha. rewrite length_Z_to_le_bytes in Ha. apply V_lib. exists 0xbfbdc0, 0xbfc1f8. split; [cbn [In LIB_PRISTINE]; tauto | lia]. }
  lit_cells 14%uint63 rg_14 G (kbs_Z 8 0x1c0a60 ++ kbs_Z 1080 0) (le8 (Z_to_bv 64 0x1c0a60) ++ Z_to_le_bytes 1080 0).
  - apply Forall2_app; apply kbs_Z_intro; lia.
  - intros _. exact (proj1 (seg_rw_ok_sound bsegs _ _ seg_rw_pthread m)).
Qed.

Lemma rg16_ok : region_ok bsegs rho 16%uint63 rg_16 m.
Proof. exact H_imgsh. Qed.

Lemma B0_facts : 0x7fff00000000 <= sp0 - to_Z ri - 262144 /\ (sp0 - to_Z ri - 262144) mod 32 = 0
  /\ 0x80177a00 <= shad (sp0 - to_Z ri - 262144) /\ shad (sp0 - to_Z ri - 262144) + (262144 + to_Z ri) / 8 <= 0x7fff00000000.
Proof.
  pose proof Hri01 as Hr. unfold USTACK_TOP in Hsp47.
  split; [lia|]. split.
  { pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32 in D.
    replace (sp0 - to_Z ri - 262144) with (0 + (sp0 / 32 - 8192) * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shad, SHB. split; Z.div_mod_to_equations; lia.
Qed.

Lemma rg3_ok : region_ok bsegs rho 3%uint63 (rg_3 ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. unfold rg_3.
  apply (zero_region_ok_d rho 3%uint63 _ 13 m (shad (sp0 - to_Z ri - 262144)) Hrho3); rewrite ?sz3.
  - lia.
  - unfold two63. lia.
  - Z.div_mod_to_equations; lia.
  - change (8 * 2 ^ Z.of_nat 13) with 65536. Z.div_mod_to_equations; lia.
  - cbn; lia.
  - exact Z_stk.
Qed.

Lemma rg2_ok : region_ok bsegs rho 2%uint63 (rg_2 ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. unfold rg_2, USTACK_TOP in *.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho2, ?sz2.
  - lia.
  - unfold two63. lia.
  - lia.
  - change (8 * 2 ^ Z.of_nat 16) with 524288. lia.
  - cbn; lia.
  - closed_side.
  - change (to_Z 5%uint63) with 5. change (2 ^ 5) with 32. exact F2.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - to_Z ri - 262144 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

Definition ivr (t : int) (rg : region) : Z * Z := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)).

Local Ltac sep :=
  unfold ivr, rbase; cbn [rg_abs rg_size rg_2 rg_3 rg_4 rg_5 rg_6 rg_7 rg_8 rg_9 rg_10 rg_11 rg_12 rg_13 rg_14 rg_15 rg_16];
  rewrite ?Hrho2, ?Hrho3, ?sz2, ?sz3;
  repeat match goal with |- context [to_Z ?x] => lazymatch x with ri => fail | _ => idtac end; is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; lia|]); constructor.

Lemma rmem0 : Rmem bsegs rho (M0 ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. unfold USTACK_TOP in *.
  pose proof (Rmem_empty bsegs rho m) as R3x. pose proof (dir_in_empty rho) as I3x.
  assert (RI4 : Rmem bsegs rho M0_4 m /\ dir_in rho M0_4 ([ivr 4%uint63 rg_4])).
  { unfold M0_4. apply (Rmem_add_sep bsegs rho IEmpty 4%uint63 rg_4 m ([]) R3x I3x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg4_ok | sep]. }
  destruct RI4 as [R4x I4x]. clear R3x I3x.
  assert (RI5 : Rmem bsegs rho M0_5 m /\ dir_in rho M0_5 ([ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_5. apply (Rmem_add_sep bsegs rho M0_4 5%uint63 rg_5 m ([ivr 4%uint63 rg_4]) R4x I4x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg5_ok | sep]. }
  destruct RI5 as [R5x I5x]. clear R4x I4x.
  assert (RI6 : Rmem bsegs rho M0_6 m /\ dir_in rho M0_6 ([ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_6. apply (Rmem_add_sep bsegs rho M0_5 6%uint63 rg_6 m ([ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R5x I5x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg6_ok | sep]. }
  destruct RI6 as [R6x I6x]. clear R5x I5x.
  assert (RI7 : Rmem bsegs rho M0_7 m /\ dir_in rho M0_7 ([ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_7. apply (Rmem_add_sep bsegs rho M0_6 7%uint63 rg_7 m ([ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R6x I6x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg7_ok | sep]. }
  destruct RI7 as [R7x I7x]. clear R6x I6x.
  assert (RI8 : Rmem bsegs rho M0_8 m /\ dir_in rho M0_8 ([ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_8. apply (Rmem_add_sep bsegs rho M0_7 8%uint63 rg_8 m ([ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R7x I7x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg8_ok | sep]. }
  destruct RI8 as [R8x I8x]. clear R7x I7x.
  assert (RI9 : Rmem bsegs rho M0_9 m /\ dir_in rho M0_9 ([ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_9. apply (Rmem_add_sep bsegs rho M0_8 9%uint63 rg_9 m ([ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R8x I8x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg9_ok | sep]. }
  destruct RI9 as [R9x I9x]. clear R8x I8x.
  assert (RI10 : Rmem bsegs rho M0_10 m /\ dir_in rho M0_10 ([ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_10. apply (Rmem_add_sep bsegs rho M0_9 10%uint63 rg_10 m ([ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R9x I9x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg10_ok | sep]. }
  destruct RI10 as [R10x I10x]. clear R9x I9x.
  assert (RI11 : Rmem bsegs rho M0_11 m /\ dir_in rho M0_11 ([ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_11. apply (Rmem_add_sep bsegs rho M0_10 11%uint63 rg_11 m ([ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R10x I10x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg11_ok | sep]. }
  destruct RI11 as [R11x I11x]. clear R10x I10x.
  assert (RI12 : Rmem bsegs rho M0_12 m /\ dir_in rho M0_12 ([ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_12. apply (Rmem_add_sep bsegs rho M0_11 12%uint63 rg_12 m ([ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R11x I11x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg12_ok | sep]. }
  destruct RI12 as [R12x I12x]. clear R11x I11x.
  assert (RI13 : Rmem bsegs rho M0_13 m /\ dir_in rho M0_13 ([ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_13. apply (Rmem_add_sep bsegs rho M0_12 13%uint63 rg_13 m ([ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R12x I12x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg13_ok | sep]. }
  destruct RI13 as [R13x I13x]. clear R12x I12x.
  assert (RI14 : Rmem bsegs rho M0_14 m /\ dir_in rho M0_14 ([ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_14. apply (Rmem_add_sep bsegs rho M0_13 14%uint63 rg_14 m ([ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R13x I13x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg14_ok | sep]. }
  destruct RI14 as [R14x I14x]. clear R13x I13x.
  assert (RI15 : Rmem bsegs rho M0_15 m /\ dir_in rho M0_15 ([ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_15. apply (Rmem_add_sep bsegs rho M0_14 15%uint63 rg_15 m ([ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R14x I14x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg15_ok | sep]. }
  destruct RI15 as [R15x I15x]. clear R14x I14x.
  assert (RI16 : Rmem bsegs rho M0_16 m /\ dir_in rho M0_16 ([ivr 16%uint63 rg_16; ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_16. apply (Rmem_add_sep bsegs rho M0_15 16%uint63 rg_16 m ([ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R15x I15x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg16_ok | sep]. }
  destruct RI16 as [R16x I16x]. clear R15x I15x.
  assert (RIs : Rmem bsegs rho (M0_3 ri) m /\ dir_in rho (M0_3 ri) ([ivr 3%uint63 (rg_3 ri); ivr 16%uint63 rg_16; ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4])).
  { unfold M0_3, M0_abs. apply (Rmem_add_sep bsegs rho M0_16 3%uint63 (rg_3 ri) m ([ivr 16%uint63 rg_16; ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) R16x I16x); [vm_compute; reflexivity | vm_compute; reflexivity | exact rg3_ok | sep]. }
  destruct RIs as [Rsx Isx].
  unfold M0. apply (Rmem_add_sep bsegs rho (M0_3 ri) 2%uint63 (rg_2 ri) m ([ivr 3%uint63 (rg_3 ri); ivr 16%uint63 rg_16; ivr 15%uint63 rg_15; ivr 14%uint63 rg_14; ivr 13%uint63 rg_13; ivr 12%uint63 rg_12; ivr 11%uint63 rg_11; ivr 10%uint63 rg_10; ivr 9%uint63 rg_9; ivr 8%uint63 rg_8; ivr 7%uint63 rg_7; ivr 6%uint63 rg_6; ivr 5%uint63 rg_5; ivr 4%uint63 rg_4]) Rsx Isx); [destruct H_ri as [-> | ->]; vm_compute; reflexivity | vm_compute; reflexivity | exact rg2_ok | sep].
Qed.

End Handoff.
