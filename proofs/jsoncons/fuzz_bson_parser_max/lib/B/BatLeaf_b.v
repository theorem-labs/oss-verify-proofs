(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r65f44_65f5c_b Ba0_code_r67bcc_67d3c_b Ba0_code_r6bbd4_6bc28_b Ba0_code_r60dd4_61420_b Ba0_code_r80560_806c8_b Ba0_code_r66e54_66ef4_b
  Ba0_code_r8d0d0_8d0e8_b Ba0_code_r61f50_61f68_b Ba0_code_rcd208_cd224_b Ba0_code_r69654_69674_b Ba0_code_r68820_68858_b Ba0_code_r69818_698c8_b
  Ba0_code_r6de28_6df9c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_asan_inited_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x140918 1 1 ->
  msteps ASEGS (mkst regs (0x801d4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_7fdbc D_7fdbc.
  zlb F_7fdc0 D_7fdc0 0x140918 C.
  stepfence F_7fdc4 D_7fdc4.
  zstep F_7fdc8 D_7fdc8.
  zstep F_7fdcc D_7fdcc.
  stepret F_7fdd0 D_7fdd0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rss_limit_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c1ea2 1 0 ->
  msteps ASEGS (mkst regs (0x85e9c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_85a84 D_85a84.
  zlb F_85a88 D_85a88 0x1c1ea2 C.
  zstep F_85a8c D_85a8c.
  stepret F_85a90 D_85a90 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_may_return_null_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x1c1ea1 1 1 ->
  msteps ASEGS (mkst regs (0x85e74 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_85a5c D_85a5c.
  zlb F_85a60 D_85a60 0x1c1ea1 C.
  zstep F_85a64 D_85a64.
  stepret F_85a68 D_85a68 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_can_poison_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x13f49c 1 1 ->
  msteps ASEGS (mkst regs (0x7ab24 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_7a70c D_7a70c.
  zlb F_7a710 D_7a710 0x13f49c C.
  stepfence F_7a714 D_7a714.
  zstep F_7a718 D_7a718.
  stepret F_7a71c D_7a71c raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_malloc_ctx_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> cellA M 0x14093c 4 30 ->
  msteps ASEGS (mkst regs (0x81e6c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 30)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret C.
  zstep F_81a54 D_81a54.
  zlw F_81a58 D_81a58 0x14093c C.
  stepfence F_81a5c D_81a5c.
  stepret F_81a60 D_81a60 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_get_pc_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw ->
  msteps ASEGS (mkst regs (0x9a948 : word) M rom) (mkst (regupd regs 10 raw) raw M rom).
Proof.
  intros regs M rom raw H1 Hret.
  zstep F_9a530 D_9a530.
  stepret F_9a534 D_9a534 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_try_init_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> cellA M 0x140918 1 1 -> apart (sp - 16) 16 0x140918 1 ->
  msteps ASEGS (mkst regs (0x810e4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 Hsp Hsp' W C Ap.
  zstep F_80ccc D_80ccc.
  zsd F_80cd0 D_80cd0 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_80cd4 D_80cd4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zstep F_80cd8 D_80cd8. zstep F_80cdc D_80cdc.
  assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x140918 1 1) by (unfold apart in *; recell C).
  zlb F_80ce0 D_80ce0 0x140918 C1.
  zstep F_80ce4 D_80ce4.
  stepfence F_80ce8 D_80ce8.
  zbft F_80cec D_80cec.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
  zld F_80cf0 D_80cf0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zld F_80cf4 D_80cf4 (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
  zstep F_80cf8 D_80cf8.
  stepret F_80cfc D_80cfc raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_lsan_off_fn : forall regs (M rom : word -> option byte) (raw : word) (tp off : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 0 <= tp -> tp + 4096 < 2 ^ 64 -> 0 <= off -> tp + off + 4 < 2 ^ 64 ->
  cellA M 0x138120 8 off -> cellA M (tp + off) 4 0 ->
  msteps ASEGS (mkst regs (0xa74c4 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
  zstep F_a70ac D_a70ac.
  zld F_a70b0 D_a70b0 0x138120 Cg.
  zstep F_a70b4 D_a70b4.
  zlw F_a70b8 D_a70b8 (tp + off) Ct.
  zstep F_a70bc D_a70bc.
  stepret F_a70c0 D_a70c0 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_tsd_get_fn : forall regs (M rom : word -> option byte) (raw : word) (tp key tsd ctx : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 4 = Z_to_bv 64 tp -> 4096 <= tp -> tp + 4096 < 2 ^ 64 ->
  0 <= key < 128 -> 0 <= tsd -> tsd + 1024 < 2 ^ 64 -> 0 <= ctx < 2 ^ 64 ->
  cellA M 0x13f4a0 1 1 -> cellA M 0x13f4a4 4 key -> cellA M (tp - 88) 8 tsd -> cellA M (tsd + 8 * key) 8 ctx ->
  msteps ASEGS (mkst regs (0x7bf64 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 ctx)) 11 (Z_to_bv 64 tsd)) raw M rom).
Proof.
  intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
  zstep F_7bb4c D_7bb4c. zstep F_7bb50 D_7bb50.
  zlbu F_7bb54 D_7bb54 0x13f4a0 Ci.
  zbft F_7bb58 D_7bb58.
  zlw F_7bb5c D_7bb5c 0x13f4a4 Ck.
  stepn F_7bb60 D_7bb60.
  zstep F_129f3c D_129f3c.
  zld F_129f40 D_129f40 (tp - 88) Ctsd.
  zstep F_129f44 D_129f44.
  stepn F_129f48 D_129f48. rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
  zstep F_129f4c D_129f4c.
  zld F_129f50 D_129f50 (tsd + 8 * key) Cctx.
  stepret F_129f54 D_129f54 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
  cellA M 0x13f4a0 1 1 /\ cellA M 0x13f4a4 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
  /\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.

#[using="Type"] Lemma art_tsd_Wn : forall n M a v tp key tsd ctx t,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  apart a (Z.of_nat n) 0x13f4a0 8 -> apart a (Z.of_nat n) (tp - 88) 8 -> apart a (Z.of_nat n) (tsd + 8 * key) 8 -> apart a (Z.of_nat n) (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd (Wn n M a v) tp key tsd ctx t.
Proof.
  intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
  unfold art_tsd. unfold apart in *.
  repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_cur_thread_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 16 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 16) 16 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 16) 16 0x13f4a0 8 -> apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x838e4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 t)) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 M (sp - 8) (U raw)) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
  pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
                ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
    as (C1 & C2 & C3 & C4 & C5 & R).
  zstep F_834cc D_834cc.
  zsd F_834d0 D_834d0 (sp - 8) (U raw) ltac:(rewok W).
  stepn F_834d4 D_834d4.
  zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
  zbft F_834d8 D_834d8.
  zld F_834dc D_834dc (ctx + 152) C5.
  assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
  zld F_834e0 D_834e0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_834e4 D_834e4.
  stepret F_834e8 D_834e8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_thread_stats_fn : forall regs (M rom : word -> option byte) (raw : word) (sp tp key tsd ctx t : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> 32 <= sp -> sp < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 32) 32 0x13f4a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x82ab0 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 10 (Z_to_bv 64 (t + 2800))) 11 (Z_to_bv 64 tsd))
                     raw (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0x82abc) rom).
Proof.
  intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  zstep F_82698 D_82698.
  zsd F_8269c D_8269c (sp - 8) (U raw) ltac:(rewok W).
  stepn F_826a0 D_826a0.
  zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
  { apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
  zbft F_826a4 D_826a4.
  zstep F_826a8 D_826a8. zstep F_826ac D_826ac.
  assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x82abc : word))) (sp - 8) 8 (U raw)).
  { apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
  zld F_826b0 D_826b0 (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
  zstep F_826b4 D_826b4.
  stepret F_826b8 D_826b8 raw ltac:(rwH; reflexivity).
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_stack_top_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x83aa8 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 top)) 11 (Z_to_bv 64 top)) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_83690 D_83690 (t + 40) C40.
  stepfence F_83694 D_83694.
  zbtk F_83698 D_83698.
  zld F_836d0 D_836d0 (t + 8) C8.
  zld F_836d4 D_836d4 (t + 16) C16.
  zstep F_836d8 D_836d8. zstep F_836dc D_836dc.
  stepn F_836e0 D_836e0. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
  stepret F_836e4 D_836e4 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_stack_bottom_fn : forall regs (M rom : word -> option byte) (raw : word) (t top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 t -> 4096 <= t -> t + 4096 < 2 ^ 64 -> 0 <= bot < top -> top < 2 ^ 64 ->
  cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  msteps ASEGS (mkst regs (0x83b00 : word) M rom) (mkst (regupd (regupd regs 10 (Z_to_bv 64 bot)) 11 (Z_to_bv 64 (2 ^ 64 - 1))) raw M rom).
Proof.
  intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
  zlb F_836e8 D_836e8 (t + 40) C40.
  stepfence F_836ec D_836ec.
  zbtk F_836f0 D_836f0.
  zld F_83728 D_83728 (t + 8) C8.
  zld F_8372c D_8372c (t + 16) C16.
  zstep F_83730 D_83730. zstep F_83734 D_83734.
  stepn F_83738 D_83738. rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
  stepret F_8373c D_8373c raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
