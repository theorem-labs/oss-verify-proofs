(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac BrtLeaf BrtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_4183c_42d28 Bo0_code_3f2bc_408d0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BrtPopulate1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Definition art_efas_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).

(* [comment removed for export] *)
Definition art_efas_c_mem (M : word -> option byte) (sp t r m1 m2 len nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 48 - 8) 263716) (sp - 48 - 24) 429116) (t + 2872) (m1 + 1)) (t + 2880) (m2 + len)) (r + 24) nm.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_efas_warm_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r total mfa : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x634000 + 48 <= sp -> 0x634000 <= r -> r + 128 < 2 ^ 47 -> 0 <= total -> 4 * total <= mfa -> mfa < 2 ^ 64 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa ->
  msteps ASEGS (mkst regs (0x40564 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 1)) 13 (Z_to_bv 64 1)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 (total * 2 ^ 2))) 18 (getr regs 18)) 19 (getr regs 19)) raw (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp r total mfa H1 Hret H2 H11 H13 Hsp Hsp' IMG Hr Hr' Htot Hmfa Hmfa' A W Cmfa.
  zstep F_40564 D_40564.
  zsd F_40568 D_40568 (sp - 8) (U raw) ltac:(rewok W). zsd F_4056c D_4056c (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_40570 D_40570 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_40574 D_40574 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_40578 D_40578 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  zld F_4057c D_4057c (r + 24) Cmfa'.
  zstep F_40580 D_40580. zstep F_40584 D_40584.
  zbtk F_40588 D_40588.
  zstep F_40648 D_40648.
  assert (F8 : cellA (art_efas_frame M sp raw regs) (sp - 8) 8 (U raw)) by (unfold art_efas_frame; zcell).
  assert (F16 : cellA (art_efas_frame M sp raw regs) (sp - 16) 8 (U (getr regs 8))) by (unfold art_efas_frame; zcell).
  assert (F24 : cellA (art_efas_frame M sp raw regs) (sp - 24) 8 (U (getr regs 9))) by (unfold art_efas_frame; zcell).
  assert (F32 : cellA (art_efas_frame M sp raw regs) (sp - 32) 8 (U (getr regs 18))) by (unfold art_efas_frame; zcell).
  assert (F40 : cellA (art_efas_frame M sp raw regs) (sp - 40) 8 (U (getr regs 19))) by (unfold art_efas_frame; zcell).
  zld F_4064c D_4064c (sp - 8) F8. zld F_40650 D_40650 (sp - 16) F16. zld F_40654 D_40654 (sp - 24) F24. zld F_40658 D_40658 (sp - 32) F32. zld F_4065c D_4065c (sp - 40) F40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_40660 D_40660.
  stepret F_40664 D_40664 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia r rb total mfa q rr : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 r -> getr regs 12 = Z_to_bv 64 rb -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x634000 + 48 <= sp -> 0 <= ia -> ia + 4096 <= 0x634000 -> 0x634000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 ->
  0 <= total -> 0 <= mfa < 4 * total -> 4 * total + 262143 = 262144 * q + rr -> 0 <= rr < 262144 -> 262144 * q <= 536870912 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa -> cellA M (ia + 56) 1 0 ->
  msteps ASEGS (mkst regs (0x40564 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x40604 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 (q * 2 ^ 18))) 9 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 11 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 12 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 13 (Z_to_bv 64 104092)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 3758096384)) 18 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 19 (Z_to_bv 64 r)) (0x7bd30 : word) (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia r rb total mfa q rr H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hia Hia' Hr Hr' Hrb Hrb' Htot Hmfa Eq Hrr Hq A W Cmfa Cpm.
  zstep F_40564 D_40564.
  zsd F_40568 D_40568 (sp - 8) (U raw) ltac:(rewok W). zsd F_4056c D_4056c (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_40570 D_40570 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_40574 D_40574 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_40578 D_40578 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  assert (Cpm' : cellA (art_efas_frame M sp raw regs) (ia + 56) 1 0) by (unfold art_efas_frame; zcell).
  zld F_4057c D_4057c (r + 24) Cmfa'.
  zstep F_40580 D_40580. zstep F_40584 D_40584.
  zbft F_40588 D_40588.
  zstep F_4058c D_4058c. zstep F_40590 D_40590. zstep F_40594 D_40594. zstep F_40598 D_40598.
  stepn F_4059c D_4059c. rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia.
  replace ((total * 2 ^ 2 + 262143) / 2 ^ 18) with q by (apply (Z.div_unique_pos _ _ q rr); lia).
  zstep F_405a0 D_405a0. zstep F_405a4 D_405a4.
  zbft F_405a8 D_405a8.
  zlbu F_405ac D_405ac (ia + 56) Cpm'.
  zstep F_405b0 D_405b0. zstep F_405b4 D_405b4. zstep F_405b8 D_405b8. zstep F_405bc D_405bc.
  zbtk F_405c0 D_405c0.
  zstep F_405e8 D_405e8. zstep F_405ec D_405ec. zstep F_405f0 D_405f0. zstep F_405f4 D_405f4. zstep F_405f8 D_405f8. zstep F_405fc D_405fc.
  stepn F_40600 D_40600.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_b_fn : forall regs (M rom : word -> option byte) (p len : Z),
  getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 len -> 0 < p < 2 ^ 64 ->
  msteps ASEGS (mkst regs (0x40604 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x40620 : bv 64)%bv) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 len)) 12 (Z_to_bv 64 250)) 14 (Z_to_bv 64 p)) (0x611f8 : word) M rom).
Proof.
  intros regs M rom p len H10 H9 H18 Hp.
  zbft F_40604 D_40604. zstep F_40608 D_40608. zbft F_4060c D_4060c.
  zstep F_40610 D_40610. zstep F_40614 D_40614. zstep F_40618 D_40618.
  stepn F_4061c D_4061c.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_c_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 nm -> getr regs 18 = Z_to_bv 64 len -> getr regs 19 = Z_to_bv 64 r ->
  80 <= sp -> sp < 2 ^ 64 -> 0x634000 + 80 <= sp -> 0x634000 <= r -> r + 128 < 2 ^ 47 -> 0 <= nm < 2 ^ 64 -> 0 <= len -> ret_ok raw ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 ->
  wrA M (sp - 80) 32 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 80) 80 0xddfa0 8 -> apart (sp - 80) 80 (tp - 88) 8 -> apart (sp - 80) 80 (tsd + 8 * key) 8 -> apart (sp - 80) 80 (ctx + 152) 8 ->
  apart (sp - 80) 80 (t + 2872) 16 -> apart (sp - 80) 80 r 128 -> apart (t + 2872) 16 r 128 ->
  wrA M (t + 2872) 16 -> wrA M r 128 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 ->
  msteps ASEGS (mkst regs (0x40620 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 r)) 12 (Z_to_bv 64 (m1 + 1))) 13 (Z_to_bv 64 1)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19))
          raw (art_efas_c_mem M sp t r m1 m2 len nm) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 H2 H4 H8 H18 H19 Hsp Hsp' IMG Hr Hr' Hnm Hlen Hret Hm1 Hm2 Ht Ht' Hg8 Hg9 Hg18 Hg19
         W TSD A1 A2 A3 A4 A5 A6 A7 Wt Wr C1 C2 F8 F16 F24 F32 F40.
  stepn F_40620 D_40620.
  zcall (art_thread_stats_fn _ _ _ _ (sp - 48) tp key tsd ctx t).
  change (U (263716 : bv 64)%bv) with 263716.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
  assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 80) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
  { intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
  assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
  assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
  zld F_40624 D_40624 (t + 2880) C2'. zld F_40628 D_40628 (t + 2872) C1'.
  zstep F_4062c D_4062c. zstep F_40630 D_40630.
  zsd F_40634 D_40634 (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zsd F_40638 D_40638 (t + 2880) (m2 + len) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zstep F_4063c D_4063c.
  zsd F_40640 D_40640 (r + 24) nm ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
  zstep F_40644 D_40644. zstep F_40648 D_40648.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
  assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 48 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
  { intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A5, A6. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
  assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
  assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
  assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
  assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
  assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
  zld F_4064c D_4064c (sp - 8) E8. zld F_40650 D_40650 (sp - 16) E16. zld F_40654 D_40654 (sp - 24) E24. zld F_40658 D_40658 (sp - 32) E32. zld F_4065c D_4065c (sp - 40) E40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_40660 D_40660.
  stepret F_40664 D_40664 raw ltac:(rwH; reflexivity).
  unfold art_efas_c_mem. subst ME MT. zret.
Qed.
End FPX.
