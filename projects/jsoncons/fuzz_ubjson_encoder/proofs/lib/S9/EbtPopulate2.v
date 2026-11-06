(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r41498_42984 Eb0_code_r3ef18_4052c.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtPopulate1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Definition art_efas_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).

Definition art_efas_c_mem (M : word -> option byte) (sp t r m1 m2 len nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 48 - 8) 353832) (sp - 48 - 24) 539752) (t + 2872) (m1 + 1)) (t + 2880) (m2 + len)) (r + 24) nm.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_efas_warm_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r total mfa : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 48 <= sp -> 0x69c000 <= r -> r + 128 < 2 ^ 47 -> 0 <= total -> 4 * total <= mfa -> mfa < 2 ^ 64 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa ->
  msteps ASEGS (mkst regs (0x56568 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 1)) 13 (Z_to_bv 64 1)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 (total * 2 ^ 2))) 18 (getr regs 18)) 19 (getr regs 19)) raw (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp r total mfa H1 Hret H2 H11 H13 Hsp Hsp' IMG Hr Hr' Htot Hmfa Hmfa' A W Cmfa.
  zstep F_56518 D_56518.
  zsd F_5651c D_5651c (sp - 8) (U raw) ltac:(rewok W). zsd F_56520 D_56520 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_56524 D_56524 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_56528 D_56528 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_5652c D_5652c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  zld F_56530 D_56530 (r + 24) Cmfa'.
  zstep F_56534 D_56534. zstep F_56538 D_56538.
  zbtk F_5653c D_5653c.
  zstep F_565fc D_565fc.
  assert (F8 : cellA (art_efas_frame M sp raw regs) (sp - 8) 8 (U raw)) by (unfold art_efas_frame; zcell).
  assert (F16 : cellA (art_efas_frame M sp raw regs) (sp - 16) 8 (U (getr regs 8))) by (unfold art_efas_frame; zcell).
  assert (F24 : cellA (art_efas_frame M sp raw regs) (sp - 24) 8 (U (getr regs 9))) by (unfold art_efas_frame; zcell).
  assert (F32 : cellA (art_efas_frame M sp raw regs) (sp - 32) 8 (U (getr regs 18))) by (unfold art_efas_frame; zcell).
  assert (F40 : cellA (art_efas_frame M sp raw regs) (sp - 40) 8 (U (getr regs 19))) by (unfold art_efas_frame; zcell).
  zld F_56600 D_56600 (sp - 8) F8. zld F_56604 D_56604 (sp - 16) F16. zld F_56608 D_56608 (sp - 24) F24. zld F_5660c D_5660c (sp - 32) F32. zld F_56610 D_56610 (sp - 40) F40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_56614 D_56614.
  stepret F_56618 D_56618 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_efas_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia r rb total mfa q rr : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 r -> getr regs 12 = Z_to_bv 64 rb -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 48 <= sp -> 0 <= ia -> ia + 4096 <= 0x69c000 -> 0x69c000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 ->
  0 <= total -> 0 <= mfa < 4 * total -> 4 * total + 262143 = 262144 * q + rr -> 0 <= rr < 262144 -> 262144 * q <= 536870912 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa -> cellA M (ia + 56) 1 0 ->
  msteps ASEGS (mkst regs (0x56568 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x56608 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 (q * 2 ^ 18))) 9 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 11 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 12 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 13 (Z_to_bv 64 105549)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 3758096384)) 18 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 19 (Z_to_bv 64 r)) (0x96d78 : word) (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia r rb total mfa q rr H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hia Hia' Hr Hr' Hrb Hrb' Htot Hmfa Eq Hrr Hq A W Cmfa Cpm.
  zstep F_56518 D_56518.
  zsd F_5651c D_5651c (sp - 8) (U raw) ltac:(rewok W). zsd F_56520 D_56520 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_56524 D_56524 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_56528 D_56528 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_5652c D_5652c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  assert (Cpm' : cellA (art_efas_frame M sp raw regs) (ia + 56) 1 0) by (unfold art_efas_frame; zcell).
  zld F_56530 D_56530 (r + 24) Cmfa'.
  zstep F_56534 D_56534. zstep F_56538 D_56538.
  zbft F_5653c D_5653c.
  zstep F_56540 D_56540. zstep F_56544 D_56544. zstep F_56548 D_56548. zstep F_5654c D_5654c.
  stepn F_56550 D_56550. rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia.
  replace ((total * 2 ^ 2 + 262143) / 2 ^ 18) with q by (apply (Z.div_unique_pos _ _ q rr); lia).
  zstep F_56554 D_56554. zstep F_56558 D_56558.
  zbft F_5655c D_5655c.
  zlbu F_56560 D_56560 (ia + 56) Cpm'.
  zstep F_56564 D_56564. zstep F_56568 D_56568. zstep F_5656c D_5656c. zstep F_56570 D_56570.
  zbtk F_56574 D_56574.
  zstep F_5659c D_5659c. zstep F_565a0 D_565a0. zstep F_565a4 D_565a4. zstep F_565a8 D_565a8. zstep F_565ac D_565ac. zstep F_565b0 D_565b0.
  stepn F_565b4 D_565b4.
  zret.
Qed.

#[using="Type"] Lemma art_efas_b_fn : forall regs (M rom : word -> option byte) (p len : Z),
  getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 len -> 0 < p < 2 ^ 64 ->
  msteps ASEGS (mkst regs (0x56608 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x56624 : bv 64)%bv) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 len)) 12 (Z_to_bv 64 250)) 14 (Z_to_bv 64 p)) (0x7bce4 : word) M rom).
Proof.
  intros regs M rom p len H10 H9 H18 Hp.
  zbft F_565b8 D_565b8. zstep F_565bc D_565bc. zbft F_565c0 D_565c0.
  zstep F_565c4 D_565c4. zstep F_565c8 D_565c8. zstep F_565cc D_565cc.
  stepn F_565d0 D_565d0.
  zret.
Qed.

#[using="Type"] Lemma art_efas_c_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 nm -> getr regs 18 = Z_to_bv 64 len -> getr regs 19 = Z_to_bv 64 r ->
  80 <= sp -> sp < 2 ^ 64 -> 0x69c000 + 80 <= sp -> 0x69c000 <= r -> r + 128 < 2 ^ 47 -> 0 <= nm < 2 ^ 64 -> 0 <= len -> ret_ok raw ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 ->
  wrA M (sp - 80) 32 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 80) 80 0x145960 8 -> apart (sp - 80) 80 (tp - 88) 8 -> apart (sp - 80) 80 (tsd + 8 * key) 8 -> apart (sp - 80) 80 (ctx + 152) 8 ->
  apart (sp - 80) 80 (t + 2872) 16 -> apart (sp - 80) 80 r 128 -> apart (t + 2872) 16 r 128 ->
  wrA M (t + 2872) 16 -> wrA M r 128 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 ->
  msteps ASEGS (mkst regs (0x56624 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 r)) 12 (Z_to_bv 64 (m1 + 1))) 13 (Z_to_bv 64 1)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19))
          raw (art_efas_c_mem M sp t r m1 m2 len nm) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 H2 H4 H8 H18 H19 Hsp Hsp' IMG Hr Hr' Hnm Hlen Hret Hm1 Hm2 Ht Ht' Hg8 Hg9 Hg18 Hg19
         W TSD A1 A2 A3 A4 A5 A6 A7 Wt Wr C1 C2 F8 F16 F24 F32 F40.
  stepn F_565d4 D_565d4.
  zcall (art_thread_stats_fn _ _ _ _ (sp - 48) tp key tsd ctx t).
  change (U (353832 : bv 64)%bv) with 353832.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
  assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 80) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
  { intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
  assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
  assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
  zld F_565d8 D_565d8 (t + 2880) C2'. zld F_565dc D_565dc (t + 2872) C1'.
  zstep F_565e0 D_565e0. zstep F_565e4 D_565e4.
  zsd F_565e8 D_565e8 (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zsd F_565ec D_565ec (t + 2880) (m2 + len) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zstep F_565f0 D_565f0.
  zsd F_565f4 D_565f4 (r + 24) nm ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
  zstep F_565f8 D_565f8. zstep F_565fc D_565fc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
  assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 48 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
  { intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A5, A6. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
  assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
  assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
  assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
  assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
  assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
  zld F_56600 D_56600 (sp - 8) E8. zld F_56604 D_56604 (sp - 16) E16. zld F_56608 D_56608 (sp - 24) E24. zld F_5660c D_5660c (sp - 32) E32. zld F_56610 D_56610 (sp - 40) E40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_56614 D_56614.
  stepret F_56618 D_56618 raw ltac:(rwH; reflexivity).
  unfold art_efas_c_mem. subst ME MT. zret.
Qed.
End FPX.
