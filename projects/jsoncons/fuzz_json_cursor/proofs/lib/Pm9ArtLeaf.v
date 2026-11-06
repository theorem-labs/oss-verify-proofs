(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  Pm9_code_82000_83000 Pm9_code_83000_84000 Pm9_code_87000_88000 Pm9_code_88000_89000 Pm9_code_89000_8a000 Pm9_code_8a000_8b000 Pm9_code_8b000_8c000 Pm9_code_8d000_8e000 Pm9_code_a1000_a2000 Pm9_code_ae000_af000 Pm9_code_149000_14a000

  .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15e9d8 1 1 ->
  msteps ASEGS (mkst regs (0x87774 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8772c D_8772c.
  zlb F_87730 D_87730 0x15e9d8 C.
  stepfence F_87734 D_87734.
  zstep F_87738 D_87738.
  zstep F_8773c D_8773c.
  stepret F_87740 D_87740 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1dff62 1 0 ->
  msteps ASEGS (mkst regs (0x8d43c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8d3f4 D_8d3f4.
  zlb F_8d3f8 D_8d3f8 0x1dff62 C.
  zstep F_8d3fc D_8d3fc.
  stepret F_8d400 D_8d400 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1dff61 1 1 ->
  msteps ASEGS (mkst regs (0x8d414 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8d3cc D_8d3cc.
  zlb F_8d3d0 D_8d3d0 0x1dff61 C.
  zstep F_8d3d4 D_8d3d4.
  stepret F_8d3d8 D_8d3d8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15d55c 1 1 ->
  msteps ASEGS (mkst regs (0x820c4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_8207c D_8207c.
  zlb F_82080 D_82080 0x15d55c C.
  stepfence F_82084 D_82084.
  zstep F_82088 D_82088.
  stepret F_8208c D_8208c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x15e9fc 4 30 ->
  msteps ASEGS (mkst regs (0x8940c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_893c4 D_893c4.
  zlw F_893c8 D_893c8 0x15e9fc C.
  stepfence F_893cc D_893cc.
  stepret F_893d0 D_893d0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0xa1ee8 : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_a1ea0 D_a1ea0.
  stepret F_a1ea4 D_a1ea4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x15e9d8 1 1 -> apart (sp - 16) 16 0x15e9d8 1 ->
  msteps ASEGS (mkst regs (0x88684 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_8863c D_8863c.
  zsd F_88640 D_88640 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_88644 D_88644 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_88648 D_88648. zstep F_8864c D_8864c.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x15e9d8 1 1) by (unfold apart in *; recell C).
  zlb F_88650 D_88650 0x15e9d8 C1.
  zstep F_88654 D_88654.
  stepfence F_88658 D_88658.
  zbft F_8865c D_8865c.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_88660 D_88660 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_88664 D_88664 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_88668 D_88668.
  stepret F_8866c D_8866c raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x155160 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xaea64 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_aea1c D_aea1c.
  zld F_aea20 D_aea20 0x155160 Cg.
  zstep F_aea24 D_aea24.
  zlw F_aea28 D_aea28 (tp + off) Ct.
  zstep F_aea2c D_aea2c.
  stepret F_aea30 D_aea30 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x15d560 1 1 -> cellA M 0x15d564 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x83504 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_834bc D_834bc. zstep F_834c0 D_834c0.
  zlbu F_834c4 D_834c4 0x15d560 Ci.
  zbft F_834c8 D_834c8.
  zlw F_834cc D_834cc 0x15d564 Ck.
  stepn F_834d0 D_834d0.
  zstep F_1490b0 D_1490b0.
  zld F_1490b4 D_1490b4 (tp - 88) Ctsd.
  zstep F_1490b8 D_1490b8.
  stepn F_1490bc D_1490bc. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_1490c0 D_1490c0.
  zld F_1490c4 D_1490c4 (tsd + 8 * key) Cctx.
  stepret F_1490c8 D_1490c8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x15d560 1 1 /\ cellA M 0x15d564 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x15d560 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x15d560 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x8ae84 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_8ae3c D_8ae3c.
  zsd F_8ae40 D_8ae40 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_8ae44 D_8ae44.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_8ae48 D_8ae48.
  zld F_8ae4c D_8ae4c (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_8ae50 D_8ae50 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_8ae54 D_8ae54.
  stepret F_8ae58 D_8ae58 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x15d560 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x8a050 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x8a05c) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_8a008 D_8a008.
  zsd F_8a00c D_8a00c (sp - 8) (U raw) ltac:(rewok W).
  stepn F_8a010 D_8a010.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_8a014 D_8a014.
  zstep F_8a018 D_8a018. zstep F_8a01c D_8a01c.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x8a05c : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_8a020 D_8a020 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_8a024 D_8a024.
  stepret F_8a028 D_8a028 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8b048 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8b000 D_8b000 (t + 40) C40.
  stepfence F_8b004 D_8b004.
  zbtk F_8b008 D_8b008.
  zld F_8b040 D_8b040 (t + 8) C8.
  zld F_8b044 D_8b044 (t + 16) C16.
  zstep F_8b048 D_8b048. zstep F_8b04c D_8b04c.
  stepn F_8b050 D_8b050. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_8b054 D_8b054 raw ltac:(rwH; reflexivity).
  zret.
Qed.

Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x8b0a0 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_8b058 D_8b058 (t + 40) C40.
  stepfence F_8b05c D_8b05c.
  zbtk F_8b060 D_8b060.
  zld F_8b098 D_8b098 (t + 8) C8.
  zld F_8b09c D_8b09c (t + 16) C16.
  zstep F_8b0a0 D_8b0a0. zstep F_8b0a4 D_8b0a4.
  stepn F_8b0a8 D_8b0a8. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_8b0ac D_8b0ac raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
