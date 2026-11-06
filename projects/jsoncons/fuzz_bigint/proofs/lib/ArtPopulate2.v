(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_415bc_42aa8 As0_code_3f03c_40650.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ArtPopulate1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Definition art_efas_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).

(* [comment removed for export] *)
Definition art_efas_c_mem (M : word -> option byte) (sp t r m1 m2 len nm : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 48 - 8) 263076) (sp - 48 - 24) 428476) (t + 2872) (m1 + 1)) (t + 2880) (m2 + len)) (r + 24) nm.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_efas_warm_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r total mfa : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 11 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x633000 + 48 <= sp -> 0x633000 <= r -> r + 128 < 2 ^ 47 -> 0 <= total -> 4 * total <= mfa -> mfa < 2 ^ 64 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa ->
  msteps ASEGS (mkst regs (0x402e4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 1)) 13 (Z_to_bv 64 1)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 (total * 2 ^ 2))) 18 (getr regs 18)) 19 (getr regs 19)) raw (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp r total mfa H1 Hret H2 H11 H13 Hsp Hsp' IMG Hr Hr' Htot Hmfa Hmfa' A W Cmfa.
  zstep F_402e4 D_402e4.
  zsd F_402e8 D_402e8 (sp - 8) (U raw) ltac:(rewok W). zsd F_402ec D_402ec (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_402f0 D_402f0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_402f4 D_402f4 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_402f8 D_402f8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  zld F_402fc D_402fc (r + 24) Cmfa'.
  zstep F_40300 D_40300. zstep F_40304 D_40304.
  zbtk F_40308 D_40308.
  zstep F_403c8 D_403c8.
  assert (F8 : cellA (art_efas_frame M sp raw regs) (sp - 8) 8 (U raw)) by (unfold art_efas_frame; zcell).
  assert (F16 : cellA (art_efas_frame M sp raw regs) (sp - 16) 8 (U (getr regs 8))) by (unfold art_efas_frame; zcell).
  assert (F24 : cellA (art_efas_frame M sp raw regs) (sp - 24) 8 (U (getr regs 9))) by (unfold art_efas_frame; zcell).
  assert (F32 : cellA (art_efas_frame M sp raw regs) (sp - 32) 8 (U (getr regs 18))) by (unfold art_efas_frame; zcell).
  assert (F40 : cellA (art_efas_frame M sp raw regs) (sp - 40) 8 (U (getr regs 19))) by (unfold art_efas_frame; zcell).
  zld F_403cc D_403cc (sp - 8) F8. zld F_403d0 D_403d0 (sp - 16) F16. zld F_403d4 D_403d4 (sp - 24) F24. zld F_403d8 D_403d8 (sp - 32) F32. zld F_403dc D_403dc (sp - 40) F40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_403e0 D_403e0.
  stepret F_403e4 D_403e4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia r rb total mfa q rr : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 r -> getr regs 12 = Z_to_bv 64 rb -> getr regs 13 = Z_to_bv 64 total ->
  48 <= sp -> sp < 2 ^ 64 -> 0x633000 + 48 <= sp -> 0 <= ia -> ia + 4096 <= 0x633000 -> 0x633000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 ->
  0 <= total -> 0 <= mfa < 4 * total -> 4 * total + 262143 = 262144 * q + rr -> 0 <= rr < 262144 -> 262144 * q <= 536870912 ->
  apart (sp - 48) 48 r 128 ->
  wrA M (sp - 48) 48 -> cellA M (r + 24) 8 mfa -> cellA M (ia + 56) 1 0 ->
  msteps ASEGS (mkst regs (0x402e4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x40384 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 (q * 2 ^ 18))) 9 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 11 (Z_to_bv 64 (mfa + (rb + 3758096384)))) 12 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 13 (Z_to_bv 64 104094)) 14 (Z_to_bv 64 mfa)) 15 (Z_to_bv 64 3758096384)) 18 (Z_to_bv 64 (q * 2 ^ 18 - mfa))) 19 (Z_to_bv 64 r)) (0x7bab0 : word) (art_efas_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia r rb total mfa q rr H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hia Hia' Hr Hr' Hrb Hrb' Htot Hmfa Eq Hrr Hq A W Cmfa Cpm.
  zstep F_402e4 D_402e4.
  zsd F_402e8 D_402e8 (sp - 8) (U raw) ltac:(rewok W). zsd F_402ec D_402ec (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_402f0 D_402f0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_402f4 D_402f4 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_402f8 D_402f8 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
  fold (art_efas_frame M sp raw regs).
  assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
  assert (Cpm' : cellA (art_efas_frame M sp raw regs) (ia + 56) 1 0) by (unfold art_efas_frame; zcell).
  zld F_402fc D_402fc (r + 24) Cmfa'.
  zstep F_40300 D_40300. zstep F_40304 D_40304.
  zbft F_40308 D_40308.
  zstep F_4030c D_4030c. zstep F_40310 D_40310. zstep F_40314 D_40314. zstep F_40318 D_40318.
  stepn F_4031c D_4031c. rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia.
  replace ((total * 2 ^ 2 + 262143) / 2 ^ 18) with q by (apply (Z.div_unique_pos _ _ q rr); lia).
  zstep F_40320 D_40320. zstep F_40324 D_40324.
  zbft F_40328 D_40328.
  zlbu F_4032c D_4032c (ia + 56) Cpm'.
  zstep F_40330 D_40330. zstep F_40334 D_40334. zstep F_40338 D_40338. zstep F_4033c D_4033c.
  zbtk F_40340 D_40340.
  zstep F_40368 D_40368. zstep F_4036c D_4036c. zstep F_40370 D_40370. zstep F_40374 D_40374. zstep F_40378 D_40378. zstep F_4037c D_4037c.
  stepn F_40380 D_40380.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_b_fn : forall regs (M rom : word -> option byte) (p len : Z),
  getr regs 10 = Z_to_bv 64 p -> getr regs 9 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 len -> 0 < p < 2 ^ 64 ->
  msteps ASEGS (mkst regs (0x40384 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x403a0 : bv 64)%bv) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 len)) 12 (Z_to_bv 64 250)) 14 (Z_to_bv 64 p)) (0x60f78 : word) M rom).
Proof.
  intros regs M rom p len H10 H9 H18 Hp.
  zbft F_40384 D_40384. zstep F_40388 D_40388. zbft F_4038c D_4038c.
  zstep F_40390 D_40390. zstep F_40394 D_40394. zstep F_40398 D_40398.
  stepn F_4039c D_4039c.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_efas_c_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 nm -> getr regs 18 = Z_to_bv 64 len -> getr regs 19 = Z_to_bv 64 r ->
  80 <= sp -> sp < 2 ^ 64 -> 0x633000 + 80 <= sp -> 0x633000 <= r -> r + 128 < 2 ^ 47 -> 0 <= nm < 2 ^ 64 -> 0 <= len -> ret_ok raw ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 ->
  wrA M (sp - 80) 32 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 80) 80 0xdd3a0 8 -> apart (sp - 80) 80 (tp - 88) 8 -> apart (sp - 80) 80 (tsd + 8 * key) 8 -> apart (sp - 80) 80 (ctx + 152) 8 ->
  apart (sp - 80) 80 (t + 2872) 16 -> apart (sp - 80) 80 r 128 -> apart (t + 2872) 16 r 128 ->
  wrA M (t + 2872) 16 -> wrA M r 128 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 ->
  msteps ASEGS (mkst regs (0x403a0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 r)) 12 (Z_to_bv 64 (m1 + 1))) 13 (Z_to_bv 64 1)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19))
          raw (art_efas_c_mem M sp t r m1 m2 len nm) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19 H2 H4 H8 H18 H19 Hsp Hsp' IMG Hr Hr' Hnm Hlen Hret Hm1 Hm2 Ht Ht' Hg8 Hg9 Hg18 Hg19
         W TSD A1 A2 A3 A4 A5 A6 A7 Wt Wr C1 C2 F8 F16 F24 F32 F40.
  stepn F_403a0 D_403a0.
  zcall (art_thread_stats_fn _ _ _ _ (sp - 48) tp key tsd ctx t).
  change (U (263076 : bv 64)%bv) with 263076.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
  assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 80) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
  { intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
  assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
  assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
  zld F_403a4 D_403a4 (t + 2880) C2'. zld F_403a8 D_403a8 (t + 2872) C1'.
  zstep F_403ac D_403ac. zstep F_403b0 D_403b0.
  zsd F_403b4 D_403b4 (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zsd F_403b8 D_403b8 (t + 2880) (m2 + len) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zstep F_403bc D_403bc.
  zsd F_403c0 D_403c0 (r + 24) nm ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
  zstep F_403c4 D_403c4. zstep F_403c8 D_403c8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
  assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 48 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
  { intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A5, A6. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
  assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
  assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
  assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
  assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
  assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
  zld F_403cc D_403cc (sp - 8) E8. zld F_403d0 D_403d0 (sp - 16) E16. zld F_403d4 D_403d4 (sp - 24) E24. zld F_403d8 D_403d8 (sp - 32) E32. zld F_403dc D_403dc (sp - 40) E40.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_403e0 D_403e0.
  stepret F_403e4 D_403e4 raw ltac:(rwH; reflexivity).
  unfold art_efas_c_mem. subst ME MT. zret.
Qed.
End FPX.
