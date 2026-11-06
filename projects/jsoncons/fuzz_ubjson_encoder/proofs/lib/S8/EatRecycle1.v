(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison EatSecAlloc ArtRuns ArtRunsMem EatFp EatCellEx EatImgCell EatSecRSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c Ea0_code_r5f7d0_5f958 Ea0_code_r7add0_7ae74 Ea0_code_r719f8_71a24.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_m2s_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (a : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 a -> 0 <= a <= SB - 1 -> art_layout M ->
  msteps ASEGS (mkst regs (0x79ef0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (2147450880 + a / 8))) 11 (Z_to_bv 64 2147450880)) 12 (Z_to_bv 64 2147450879)) 13 (Z_to_bv 64 2147450879)) raw M rom).
Proof.
  intros regs M rom raw a H1 Hret H10 Ha L. unfold SB in *.
  destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  stepn F_79ea0 D_79ea0.
  zld F_79ea4 D_79ea4 0x1391b8 L1.
  zld F_79ea8 D_79ea8 0x1419f8 L2.
  zstep F_79eac D_79eac. zstep F_79eb0 D_79eb0. zstep F_79eb4 D_79eb4.
  stepn F_79eb8 D_79eb8. rwH. zclosed 2147450879.
  zbtk F_79ebc D_79ebc.
  stepn F_79f00 D_79f00. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_79f04 D_79f04.
  stepret F_79f08 D_79f08 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_m2s_hi_fn : forall regs (M rom : word -> option byte) (raw : word) (a : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 a -> kHighMemBeg <= a <= kHighMemEnd -> art_layout M ->
  msteps ASEGS (mkst regs (0x79ef0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 5 (Z_to_bv 64 140737488355327)) 10 (Z_to_bv 64 (2147450880 + a / 8))) 11 (Z_to_bv 64 2147450880)) 12 (Z_to_bv 64 2147450879)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 17592186044415)) 15 (Z_to_bv 64 18446744073709551615)) 16 (Z_to_bv 64 0)) 17 (Z_to_bv 64 17594333495295)) raw M rom).
Proof.
  intros regs M rom raw a H1 Hret H10 Ha L. unfold SB, kHighMemBeg, kHighMemEnd in *.
  destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  stepn F_79ea0 D_79ea0.
  zld F_79ea4 D_79ea4 0x1391b8 L1.
  zld F_79ea8 D_79ea8 0x1419f8 L2.
  zstep F_79eac D_79eac. zstep F_79eb0 D_79eb0. zstep F_79eb4 D_79eb4.
  stepn F_79eb8 D_79eb8. rwH. zclosed 2147450879.
  zbft F_79ebc D_79ebc.
  stepn F_79ec0 D_79ec0.
  zld F_79ec4 D_79ec4 0x1391c0 L3.
  stepn F_79ec8 D_79ec8.
  zld F_79ecc D_79ecc 0x1391c8 L5.
  zld F_79ed0 D_79ed0 0x1426e8 L4.
  zld F_79ed4 D_79ed4 0x1426f0 L6.
  zstep F_79ed8 D_79ed8.
  zbtk F_79edc D_79edc.
  stepn F_79ee4 D_79ee4.
  zld F_79ee8 D_79ee8 0x1391d0 L7.
  zld F_79eec D_79eec 0x1426e0 L8.
  stepn F_79ef0 D_79ef0. rwH. zclosed 17592186044415.
  zstep F_79ef4 D_79ef4.
  zbft F_79ef8 D_79ef8.
  zbft F_79efc D_79efc.
  stepn F_79f00 D_79f00. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_79f04 D_79f04.
  stepret F_79f08 D_79f08 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.

Definition art_pg_dn (x : Z) : Z := x - x mod 4096.
Definition art_flush_beg (mb : Z) : Z := art_pg_dn (SB + mb / 8 + 4095).
Definition art_flush_end (mb ms : Z) : Z := art_pg_dn (SB + (mb + ms) / 8).

Definition art_flush_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)).

Section FPX1. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_layout_flush_frame : forall M sp raw regs, 0x698000 + 32 <= sp -> sp < 2 ^ 64 -> art_layout M -> art_layout (art_flush_frame M sp raw regs).
Proof.
  intros M sp raw regs Hsp Hsp' L. unfold art_flush_frame.
  repeat (apply art_layout_Wn; [lia|cbn; lia|unfold apart; cbn; lia|unfold apart; cbn; lia|]). exact L.
Qed.

#[using="Type"] Lemma art_flush_frame_cells : forall M sp raw regs, 32 <= sp -> sp < 2 ^ 64 ->
  let X := art_flush_frame M sp raw regs in
  cellA X (sp - 8) 8 (U raw) /\ cellA X (sp - 16) 8 (U (getr regs 8)) /\ cellA X (sp - 24) 8 (U (getr regs 9)) /\ cellA X (sp - 32) 8 (U (getr regs 18)).
Proof. intros M sp raw regs Hsp Hsp'. unfold art_flush_frame. repeat split; zcell. Qed.
#[using="Type"] Lemma art_flush_frame_other : forall M sp raw regs a n v, 32 <= sp -> sp < 2 ^ 64 -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> apart (sp - 32) 32 a (Z.of_nat n) ->
  cellA M a n v -> cellA (art_flush_frame M sp raw regs) a n v.
Proof. intros M sp raw regs a n v Hsp Hsp' Ha Hn A C. unfold art_flush_frame. unfold apart in A. repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. Qed.
#[using="Type"] Lemma art_flush_frame_wr : forall M sp raw regs a n, wrA M a n -> wrA (art_flush_frame M sp raw regs) a n.
Proof. intros. unfold art_flush_frame. repeat apply wr_Wn. assumption. Qed.

#[using="Type"] Lemma art_flush_a_lo : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> 0 <= mb /\ mb + ms <= SB - 1 -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x79ea4 : word) M rom) (mkst regs' (0x95a00 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + mb / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (mb + ms) / 8)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
  pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
  eexists. split.
  {
  zstep F_79e54 D_79e54.
  zsd F_79e58 D_79e58 (sp - 8) (U raw) ltac:(rewok W). zsd F_79e5c D_79e5c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_79e60 D_79e60 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_79e64 D_79e64 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_79e68 D_79e68. zstep F_79e6c D_79e6c.
  stepn F_79e70 D_79e70.
  change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
  pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
  zcall (art_m2s_lo_fn _ _ _ (0x79ec4 : word) mb).
  zstep F_79e74 D_79e74. zstep F_79e78 D_79e78.
  stepn F_79e7c D_79e7c.
  zcall (art_m2s_lo_fn _ _ _ (0x79ed0 : word) (ms + mb)).
  zstep F_79e80 D_79e80. zstep F_79e84 D_79e84.
  destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  zld F_79e88 D_79e88 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_79e8c D_79e8c (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_79e90 D_79e90 (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
  zld F_79e94 D_79e94 (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
  zstep F_79e98 D_79e98.
  stepn F_79e9c D_79e9c.
  apply mst_refl. }
  replace (mb + ms) with (ms + mb) by lia.
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_flush_a_hi : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> kHighMemBeg <= mb /\ mb + ms <= kHighMemEnd -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x79ea4 : word) M rom) (mkst regs' (0x95a00 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + mb / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (mb + ms) / 8)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
  pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
  eexists. split.
  {
  zstep F_79e54 D_79e54.
  zsd F_79e58 D_79e58 (sp - 8) (U raw) ltac:(rewok W). zsd F_79e5c D_79e5c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_79e60 D_79e60 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_79e64 D_79e64 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_79e68 D_79e68. zstep F_79e6c D_79e6c.
  stepn F_79e70 D_79e70.
  change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
  pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
  zcall (art_m2s_hi_fn _ _ _ (0x79ec4 : word) mb).
  zstep F_79e74 D_79e74. zstep F_79e78 D_79e78.
  stepn F_79e7c D_79e7c.
  zcall (art_m2s_hi_fn _ _ _ (0x79ed0 : word) (ms + mb)).
  zstep F_79e80 D_79e80. zstep F_79e84 D_79e84.
  destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  zld F_79e88 D_79e88 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_79e8c D_79e8c (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_79e90 D_79e90 (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
  zld F_79e94 D_79e94 (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
  zstep F_79e98 D_79e98.
  stepn F_79e9c D_79e9c.
  apply mst_refl. }
  replace (mb + ms) with (ms + mb) by lia.
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

Definition art_rel_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte := art_flush_frame M sp raw regs.

#[using="Type"] Lemma art_rel_head : forall regs (M rom : word -> option byte) (raw : word) (sp sa sb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 sb ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 -> 0 <= sa -> sa + 4096 < 2 ^ 64 -> 0 <= sb < 2 ^ 64 ->
  cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x95a00 : word) M rom) (mkst regs' (0x95a58 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (art_pg_dn (sa + 4095)) /\ getr regs' 11 = Z_to_bv 64 (art_pg_dn sb)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 32)
    /\ (forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp sa sb H1 H2 H10 H11 Hsp Hsp' W Hsa Hsa' Hsb Cpc Cpg.
  eexists. split.
  {
  zstep F_959b0 D_959b0.
  zsd F_959b4 D_959b4 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_959b8 D_959b8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_959bc D_959bc (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_959c0 D_959c0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_959c4 D_959c4.
  stepn F_959c8 D_959c8.
  match goal with |- msteps _ (mkst _ _ ?Y _) _ => assert (Cpc2 : cellA Y 0x139198 8 0x1d14a0) by zcell; assert (Cpg2 : cellA Y 0x1d14a0 8 4096) by zcell end.
  zld F_959cc D_959cc 0x139198 Cpc2.
  zld F_959d0 D_959d0 0x1d14a0 Cpg2.
  zstep F_959d4 D_959d4.
  zbtk F_959d8 D_959d8.
  zstep F_959e8 D_959e8.
  stepn F_959ec D_959ec. rwH. zclosed 0.
  zbft F_959f0 D_959f0.
  zstep F_959f4 D_959f4.
  stepn F_959f8 D_959f8. rwH. zclosed 18446744073709547520.
  zstep F_959fc D_959fc.
  replace (sa + 4096 + -1) with (sa + 4095) by lia.
  stepn F_95a00 D_95a00. rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  stepn F_95a04 D_95a04. rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  unfold art_flush_frame. apply mst_refl. }
  unfold art_pg_dn.
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rel_madv : forall regs (M rom : word -> option byte) (raw : word) (sp beg en x8 x9 x18 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 en ->
  32 <= sp -> sp < 2 ^ 64 -> 0 <= beg -> beg < en -> en < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M 0x1391f8 8 1 ->
  msteps ASEGS (mkst regs (0x95a58 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 (en - beg))) 12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 4)) 17 (Z_to_bv 64 233)) 18 (Z_to_bv 64 x18))
      (0x8c648 : word) M rom).
Proof.
  intros regs M rom raw sp beg en x8 x9 x18 H2 H10 H11 Hsp Hsp' Hb Hbe He Hx8 Hx9 Hx18 F1 F8 F9 F18 Cgot.
  zbft F_95a08 D_95a08.
  zstep F_95a0c D_95a0c. zstep F_95a10 D_95a10.
  zld F_95a14 D_95a14 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_95a18 D_95a18 (sp - 16) F8.
  zld F_95a1c D_95a1c (sp - 24) F9.
  zld F_95a20 D_95a20 (sp - 32) F18.
  zstep F_95a24 D_95a24.
  stepn F_95a28 D_95a28.
  stepn F_8c5d8 D_8c5d8.
  zld F_8c5dc D_8c5dc 0x1391f8 Cgot.
  zbft F_8c5e0 D_8c5e0.
  zstep F_8c5e4 D_8c5e4.
  zbtk F_8c5e8 D_8c5e8.
  zstep F_8c5f4 D_8c5f4.
  zret.
Qed.

#[using="Type"] Lemma art_rel_skip : forall regs (M rom : word -> option byte) (raw : word) (sp beg en x8 x9 x18 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 en -> ret_ok raw ->
  32 <= sp -> sp < 2 ^ 64 -> 0 <= en -> en <= beg -> beg < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  msteps ASEGS (mkst regs (0x95a58 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 18 (Z_to_bv 64 x18)) raw M rom).
Proof.
  intros regs M rom raw sp beg en x8 x9 x18 H2 H10 H11 Hret Hsp Hsp' He Hbe Hb Hx8 Hx9 Hx18 F1 F8 F9 F18.
  zbtk F_95a08 D_95a08.
  zld F_95a2c D_95a2c (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_95a30 D_95a30 (sp - 16) F8.
  zld F_95a34 D_95a34 (sp - 24) F9.
  zld F_95a38 D_95a38 (sp - 32) F18.
  zstep F_95a3c D_95a3c.
  stepret F_95a40 D_95a40 raw ltac:(reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_flush_post_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 0 ->
  msteps ASEGS (mkst regs (0x8c64c : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret H10.
  stepn F_8c5fc D_8c5fc. rwH. zclosed 0.
  stepret F_8c600 D_8c600 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_flush_frame_ext : forall M sp raw regs regs', getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  art_flush_frame M sp raw regs' = art_flush_frame M sp raw regs.
Proof. intros M sp raw regs regs' E8 E9 E18. unfold art_flush_frame. rewrite E8, E9, E18. reflexivity. Qed.

Definition art_blk_ok (mb ms : Z) : Prop := (0 <= mb /\ mb + ms <= SB - 1) \/ (kHighMemBeg <= mb /\ mb + ms <= kHighMemEnd).

Definition art_flush_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  art_flush_frame (art_flush_frame M sp raw regs) sp raw regs.

#[using="Type"] Lemma art_flush_a_run : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x79ea4 : word) M rom) (mkst regs' (0x95a00 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + mb / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (mb + ms) / 8)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms [B|B] L.
  - apply art_flush_a_lo; assumption.
  - apply art_flush_a_hi; assumption.
Qed.

#[using="Type"] Lemma art_blk_shadow_range : forall mb ms, 0 <= ms -> art_blk_ok mb ms ->
  0 <= mb / 8 /\ mb / 8 <= (mb + ms) / 8 /\ (mb + ms) / 8 < 2 ^ 44.
Proof.
  intros mb ms Hms B. pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
  assert (0 <= mb /\ mb + ms < 2 ^ 47) as [Hmb Hhi] by (destruct B; lia).
  split; [apply Z.div_pos; lia|]. split; [apply Z.div_le_mono; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

#[using="Type"] Lemma art_flush_pre_run : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 -> cellA M 0x1391f8 8 1 ->
  art_flush_beg mb < art_flush_end mb ms ->
  exists regs', msteps ASEGS (mkst regs (0x79ea4 : word) M rom) (mkst regs' (0x8c648 : word) (art_flush_mem M sp raw regs) rom)
    /\ art_madvise_args regs' (art_flush_beg mb) (art_flush_end mb ms - art_flush_beg mb)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Cgot Hbe.
  destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
  destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
  pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
  pose proof (art_flush_frame_other M sp raw regs 0x139198 8%nat 0x1d14a0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
  pose proof (art_flush_frame_other M sp raw regs 0x1d14a0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
  pose proof (art_flush_frame_other M sp raw regs 0x1391f8 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot) as Cgot1.
  remember (art_flush_frame M sp raw regs) as M1 eqn:EM1.
  destruct (art_rel_head r1 M1 rom raw sp (SB + mb / 8) (SB + (mb + ms) / 8) A1 A2 A10 A11 Hsp Hsp' W1 ltac:(lia) ltac:(lia) ltac:(lia) Cpc1 Cpg1)
    as (r2 & RUN2 & B10 & B11 & B2 & BK).
  rewrite (art_flush_frame_ext M1 sp raw regs r1 (AK 8%bv ltac:(cbn; tauto)) (AK 9%bv ltac:(cbn; tauto)) (AK 18%bv ltac:(cbn; tauto))) in RUN2.
  destruct (art_flush_frame_cells M1 sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  pose proof (art_flush_frame_other M1 sp raw regs 0x1391f8 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot1) as Cgot2.
  remember (art_flush_frame M1 sp raw regs) as M2 eqn:EM2.
  unfold art_flush_beg, art_flush_end in *.
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (P1 : 0 <= art_pg_dn (SB + mb / 8 + 4095)) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + mb / 8 + 4095) 4096 ltac:(lia)); lia).
  assert (P2 : art_pg_dn (SB + (mb + ms) / 8) < 2 ^ 64) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + (mb + ms) / 8) 4096 ltac:(lia)); lia).
  pose proof (art_rel_madv r2 M2 rom raw sp _ _ _ _ _ B2 B10 B11 ltac:(lia) Hsp' P1 Hbe P2 R8 R9 R18 F1 F8 F9 F18 Cgot2) as RUN3.
  assert (EM : M2 = art_flush_mem M sp raw regs) by (subst M2 M1; reflexivity). rewrite EM in RUN3, RUN2.
  eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [unfold art_madvise_args; repeat split; gres; first [reflexivity | exact B10]|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. rewrite <- (AK r Hr). cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]. destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  repeat (destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_flush_skip_run : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x698000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 ->
  art_flush_end mb ms <= art_flush_beg mb ->
  exists regs', msteps ASEGS (mkst regs (0x79ea4 : word) M rom) (mkst regs' raw (art_flush_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 Hret H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Hbe.
  destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
  destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
  pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
  pose proof (art_flush_frame_other M sp raw regs 0x139198 8%nat 0x1d14a0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
  pose proof (art_flush_frame_other M sp raw regs 0x1d14a0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
  remember (art_flush_frame M sp raw regs) as M1 eqn:EM1.
  destruct (art_rel_head r1 M1 rom raw sp (SB + mb / 8) (SB + (mb + ms) / 8) A1 A2 A10 A11 Hsp Hsp' W1 ltac:(lia) ltac:(lia) ltac:(lia) Cpc1 Cpg1)
    as (r2 & RUN2 & B10 & B11 & B2 & BK).
  rewrite (art_flush_frame_ext M1 sp raw regs r1 (AK 8%bv ltac:(cbn; tauto)) (AK 9%bv ltac:(cbn; tauto)) (AK 18%bv ltac:(cbn; tauto))) in RUN2.
  destruct (art_flush_frame_cells M1 sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  remember (art_flush_frame M1 sp raw regs) as M2 eqn:EM2.
  unfold art_flush_beg, art_flush_end in *.
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (P1 : art_pg_dn (SB + mb / 8 + 4095) < 2 ^ 64) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + mb / 8 + 4095) 4096 ltac:(lia)); lia).
  assert (P2 : 0 <= art_pg_dn (SB + (mb + ms) / 8)) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + (mb + ms) / 8) 4096 ltac:(lia)); lia).
  pose proof (art_rel_skip r2 M2 rom raw sp _ _ _ _ _ B2 B10 B11 Hret ltac:(lia) Hsp' P2 Hbe P1 R8 R9 R18 F1 F8 F9 F18) as RUN3.
  assert (EM : M2 = art_flush_mem M sp raw regs) by (subst M2 M1; reflexivity). rewrite EM in RUN3, RUN2.
  eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; reflexivity|].
  intros r Hr. rewrite <- (AK r Hr). cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]. destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
  repeat (destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_flush_mem_agree : forall M sp raw regs, 32 <= sp -> sp < 2 ^ 64 -> art_agree [(sp - 32, 32)] M (art_flush_mem M sp raw regs).
Proof.
  intros M sp raw regs Hsp Hsp'. unfold art_flush_mem, art_flush_frame.
  eapply art_agree_sub; [zagree|]. zsub.
Qed.
#[using="Type"] Lemma art_flush_mem_grows : forall M sp raw regs, mem_grows M (art_flush_mem M sp raw regs).
Proof. intros. unfold art_flush_mem, art_flush_frame. zgrows. Qed.
End FPX1.

Lemma art_pg_dn_spec : forall x, 0 <= x -> art_pg_dn x mod 4096 = 0 /\ art_pg_dn x <= x < art_pg_dn x + 4096.
Proof.
  intros x Hx. unfold art_pg_dn. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as B.
  split; [|lia]. replace (x - x mod 4096) with (x / 4096 * 4096) by lia. apply Z_mod_mult.
Qed.

Lemma art_flush_range : forall mb ms, mb mod 4096 = 0 -> ms mod 4096 = 0 -> 0 <= mb -> 0 <= ms ->
  let beg := art_flush_beg mb in let en := art_flush_end mb ms in
  beg mod 4096 = 0 /\ en mod 4096 = 0 /\ (en - beg) mod 4096 = 0
  /\ SB + mb / 8 <= beg /\ en <= SB + (mb + ms) / 8 /\ (mb + ms) / 8 = mb / 8 + ms / 8
  /\ art_shlo mb <= beg /\ en <= art_shhi mb ms
  /\ (65536 <= ms -> beg < en).
Proof.
  intros mb ms Hmb Hms Hmb0 Hms0 beg en. subst beg en. unfold art_flush_beg, art_flush_end.
  pose proof (eq_refl : SB = 2147450880) as ESB.
  assert (Er : mb = 4096 * (mb / 4096)) by (pose proof (Z.div_mod mb 4096 ltac:(lia)); lia).
  assert (Em : ms = 4096 * (ms / 4096)) by (pose proof (Z.div_mod ms 4096 ltac:(lia)); lia).
  set (kr := mb / 4096) in *. set (km := ms / 4096) in *.
  assert (D1 : mb / 8 = 512 * kr). { rewrite Er. replace (4096 * kr) with (512 * kr * 8) by lia. apply Z.div_mul. lia. }
  assert (D2 : ms / 8 = 512 * km). { rewrite Em. replace (4096 * km) with (512 * km * 8) by lia. apply Z.div_mul. lia. }
  assert (D3 : (mb + ms) / 8 = 512 * kr + 512 * km). { rewrite Er, Em. replace (4096 * kr + 4096 * km) with ((512 * kr + 512 * km) * 8) by lia. apply Z.div_mul. lia. }
  rewrite D3, D1, D2.
  destruct (art_pg_dn_spec (SB + 512 * kr + 4095) ltac:(lia)) as (P1 & P2). destruct (art_pg_dn_spec (SB + (512 * kr + 512 * km)) ltac:(lia)) as (P3 & P4).
  set (B := art_pg_dn (SB + 512 * kr + 4095)) in *. set (E := art_pg_dn (SB + (512 * kr + 512 * km))) in *.
  assert (PB : B = 4096 * (B / 4096)) by (pose proof (Z.div_mod B 4096 ltac:(lia)); lia).
  assert (PE : E = 4096 * (E / 4096)) by (pose proof (Z.div_mod E 4096 ltac:(lia)); lia).
  split; [exact P1|]. split; [exact P3|].
  split. { rewrite PB, PE. replace (4096 * (E / 4096) - 4096 * (B / 4096)) with ((E / 4096 - B / 4096) * 4096) by lia. apply Z_mod_mult. }

  assert (LB : SB + 512 * kr <= B).
  { destruct (Z_lt_le_dec B (SB + 512 * kr)) as [L|G]; [|exact G]. exfalso.
    assert (4096 * (B / 4096) + 4096 <= SB + 512 * kr + 4095) by lia. lia. }
  split; [exact LB|]. split; [lia|]. split; [reflexivity|].
  unfold art_shlo, art_shhi. rewrite D1, D3.
  pose proof (Z.div_mod (512 * kr + 2147450880) 4096 ltac:(lia)) as Q1. pose proof (Z.mod_pos_bound (512 * kr + 2147450880) 4096 ltac:(lia)) as Q2.
  pose proof (Z.div_mod (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q3. pose proof (Z.mod_pos_bound (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q4.
  set (X := (512 * kr + 2147450880) / 4096) in *. set (Y := (512 * kr + 512 * km + 2147450880 + 4095) / 4096) in *.
  split; [lia|]. split; [lia|].
  intros H64. lia.
Qed.

Fixpoint art_gbb_scan (m near : Z) (chs : list Z) : Z :=
  match chs with [] => near | ch :: r => art_gbb_scan m (if (ch <=? m) && (near <? ch) then ch else near) r end.

Lemma art_gbb_scan_range : forall chs m near, 0 <= near <= m -> Forall (fun ch => 0 <= ch) chs -> 0 <= art_gbb_scan m near chs <= m.
Proof.
  induction chs as [|ch r IH]; intros m near Hn F; cbn [art_gbb_scan]; [exact Hn|].
  inversion F as [|? ? F1 F2]; subst. apply IH; [|exact F2].
  destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia.
Qed.

Lemma art_gbb_scan_is : forall chs m h near, (In h chs \/ near = h) -> h <= m -> near <= h -> (forall ch, In ch chs -> ch <= m -> ch <= h) ->
  art_gbb_scan m near chs = h.
Proof.
  induction chs as [|ch r IH]; intros m h near Hin Hm Hn Hmax; cbn [art_gbb_scan].
  - destruct Hin as [[]|E]. exact E.
  - apply IH; [| exact Hm | | intros c Hc; apply Hmax; right; exact Hc].
    + destruct Hin as [[E|Hin]|E].
      * subst ch. right. replace (h <=? m) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
        destruct (Z.ltb_spec near h); lia.
      * left. exact Hin.
      * right. subst near. pose proof (Hmax ch ltac:(left; reflexivity)) as Hc.
        destruct (Z.leb_spec ch m); cbn [andb]; [|reflexivity]. destruct (Z.ltb_spec h ch); [lia|reflexivity].
    + pose proof (Hmax ch ltac:(left; reflexivity)) as Hc.
      destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia.
Qed.

Section FPX2. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_gbb_loop : forall chs regs (M rom : word -> option byte) (cur en m near : Z),
  getr regs 12 = Z_to_bv 64 cur -> getr regs 14 = Z_to_bv 64 en -> getr regs 11 = Z_to_bv 64 m -> getr regs 13 = Z_to_bv 64 near ->
  en = cur + 8 * Z.of_nat (length chs) -> (1 <= length chs)%nat -> 0 <= cur -> en < 2 ^ 64 -> 0 <= near <= m -> m < 2 ^ 64 ->
  (forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA M (cur + 8 * Z.of_nat j) 8 (nth j chs 0)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x553cc : word) M rom) (mkst regs' (0x553f8 : word) M rom)
    /\ getr regs' 13 = Z_to_bv 64 (art_gbb_scan m near chs)
    /\ (forall r : reg, r <> 5%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
  induction chs as [|ch chs IH]; intros regs M rom cur en m near H12 H14 H11 H13 Een Hlen Hcur Hen Hnear Hm Cws; cbn [length] in *. lia.
  destruct (Cws O ltac:(lia)) as [Rch Cch]. cbn [nth] in Rch, Cch. replace (cur + 8 * Z.of_nat 0) with cur in Cch by lia.
  set (near' := if (ch <=? m) && (near <? ch) then ch else near).
  assert (Hnear' : 0 <= near' <= m) by (subst near'; destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia).
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x553cc : word) M rom) (mkst regs1 (0x553c8 : word) M rom)
            /\ getr regs1 12 = Z_to_bv 64 (cur + 8) /\ getr regs1 13 = Z_to_bv 64 near' /\ getr regs1 14 = Z_to_bv 64 en /\ getr regs1 11 = Z_to_bv 64 m
            /\ (forall r : reg, r <> 5%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)).
  { destruct (Z.leb_spec ch m) as [Lm|Gm].
    - destruct (Z.ltb_spec near ch) as [Ln|Gn]; subst near'; cbn [andb].
      +
        eexists. split.
        { zld F_5537c D_5537c cur Cch. zstep F_55380 D_55380. zstep F_55384 D_55384. zstep F_55388 D_55388.
          zbtk F_5538c D_5538c. zbft F_5539c D_5539c. zstep F_553a0 D_553a0. stepn F_553a4 D_553a4. zstep F_55374 D_55374. apply mst_refl. }
        repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
      +
        eexists. split.
        { zld F_5537c D_5537c cur Cch. zstep F_55380 D_55380. zstep F_55384 D_55384. zstep F_55388 D_55388.
          zbft F_5538c D_5538c. zstep F_55390 D_55390. zbft F_55394 D_55394. stepn F_55398 D_55398. zstep F_553a0 D_553a0. stepn F_553a4 D_553a4. zstep F_55374 D_55374. apply mst_refl. }
        repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
    -
      subst near'. cbn [andb].
      eexists. split.
      { zld F_5537c D_5537c cur Cch. zstep F_55380 D_55380. zstep F_55384 D_55384. zstep F_55388 D_55388.
        replace (Z_to_bv 64 (m - ch)) with (Z_to_bv 64 (2 ^ 64 + m - ch)) by (apply art_zb_eq; replace (2 ^ 64 + m - ch) with (m - ch + 1 * 2 ^ 64) by lia; apply Z_mod_plus_full).
        zbft F_5538c D_5538c. zstep F_55390 D_55390. zbtk F_55394 D_55394. zstep F_55374 D_55374. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P12 & P13 & P14 & P11 & K1).
  destruct chs as [|ch2 chs2].
  -
    cbn [length] in *. eexists. split; [|split].
    + eapply msteps_trans; [exact RUN1|]. zbtk F_55378 D_55378. apply mst_refl.
    + cbn [art_gbb_scan]. exact P13.
    + exact K1.
  - cbn [length] in *.
    assert (RUNb : msteps ASEGS (mkst regs1 (0x553c8 : word) M rom) (mkst regs1 (0x553cc : word) M rom)).
    { zbft F_55378 D_55378. apply mst_refl. }
    destruct (IH regs1 M rom (cur + 8) en m near' P12 P14 P11 P13 ltac:(cbn [length]; lia) ltac:(cbn [length]; lia) ltac:(lia) Hen Hnear' Hm
                 ltac:(intros j Hj; destruct (Cws (S j) ltac:(cbn [length] in *; lia)) as [R C]; split; [exact R|];
                       replace (cur + 8 + 8 * Z.of_nat j) with (cur + 8 * Z.of_nat (S j)) by lia; exact C))
      as (regs' & RUN2 & Q13 & K2).
    exists regs'. split; [|split].
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. exact RUN2.
    + exact Q13.
    + intros r N5 N12 N13 N15 N16 N17. rewrite K2 by assumption. apply K1; assumption.
Qed.

Definition art_gbb_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 1 (Wn 4 (art_flush_frame M sp raw regs) (0x13e3d8 + 616) 1) (0x13e3d8 + 616) 0.

Ltac gkeep K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).

#[using="Type"] Lemma art_gbb_run : forall chs regs (M rom : word -> option byte) (raw : word) (sp HI m parr h mbeg msz : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13e3d8 -> getr regs 11 = Z_to_bv 64 m ->
  0x698000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  (1 <= length chs)%nat -> Z.of_nat (length chs) < 2 ^ 20 -> 0x698000 <= parr -> parr + 8 * Z.of_nat (length chs) <= HI -> 0 <= m < 2 ^ 64 ->
  cellA M (0x13e3d8 + 616) 4 0 -> cellA M (0x13e3d8 + 56) 8 (Z.of_nat (length chs)) -> cellA M (0x13e3d8 + 8) 8 parr -> cellA M 0x13e3d8 8 4096 ->
  (forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA M (parr + 8 * Z.of_nat j) 8 (nth j chs 0)) ->
  h = art_gbb_scan m 0 chs -> 0x698000 <= h -> h + 16 <= HI -> h mod 4096 = 0 ->
  cellA M h 8 mbeg -> cellA M (h + 8) 8 msz -> 0 <= mbeg <= h -> h < mbeg + msz -> m < mbeg + msz -> 0 <= msz -> mbeg + msz < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x55360 : word) M rom) (mkst regs' raw (art_gbb_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (h + 4096) /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros chs regs M rom raw sp HI m parr h mbeg msz H1 Hret H2 H10 H11 HHI Hsp Hsp' W Hn Hn' Hparr Hparr' Hm Clk Cn Cparr Cpg Cws Eh Hh Hh' Hh4 Cmb Cms Hmb Hhm Hmm Hms Hme.
  assert (Hhr : 0 <= h <= m) by (rewrite Eh; apply art_gbb_scan_range; [lia|]; apply Forall_forall; intros x Hx; destruct (In_nth _ _ 0 Hx) as (j & Hj & <-); apply (Cws j Hj)).
  pose proof (art_img_wr M (0x13e3d8 + 616) 4 ltac:(lia) ltac:(lia) ltac:(lia)) as Wlk.
  eassert (RUN1 : msteps ASEGS (mkst regs (0x55360 : word) M rom) _).
  {
    zstep F_55310 D_55310.
    zsd F_55314 D_55314 (sp - 8) (U raw) ltac:(rewok W). zsd F_55318 D_55318 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5531c D_5531c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55320 D_55320 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zstep F_55324 D_55324. zstep F_55328 D_55328.
    stepn F_5532c D_5532c. rwH. zclosed (0x13e3d8 + 616).
    zstep F_55330 D_55330.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13e3d8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x13e3d8 + 616) 4) by zwok end.
    zcas6 F_55334 D_55334 F_55338 D_55338 F_5533c D_5533c F_55340 D_55340 F_55344 D_55344 F_55348 D_55348 (0x13e3d8 + 616) 0 1 1 1 Clk' Wlk'.
    zbft F_5534c D_5534c.
    stepn F_55350 D_55350. rwH. zclosed 0.
    zbft F_55354 D_55354.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cn' : cellA X (0x13e3d8 + 56) 8 (Z.of_nat (length chs))) by zcell; assert (Cparr' : cellA X (0x13e3d8 + 8) 8 parr) by zcell end.
    zld F_55358 D_55358 (0x13e3d8 + 56) Cn'.
    zbft F_5535c D_5535c.
    zstep F_55360 D_55360.
    zld F_55364 D_55364 (0x13e3d8 + 8) Cparr'.
    zstep F_55368 D_55368. zstep F_5536c D_5536c.
    stepn F_55370 D_55370.
    apply mst_refl. }
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (Cws1 : forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA X1 (parr + 8 * Z.of_nat j) 8 (nth j chs 0))
      by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
    assert (Cmb1 : cellA X1 h 8 mbeg) by zcell; assert (Cms1 : cellA X1 (h + 8) 8 msz) by zcell; assert (Cpg1 : cellA X1 0x13e3d8 8 4096) by zcell;
    assert (F1 : cellA X1 (sp - 8) 8 (U raw)) by zcell; assert (F8 : cellA X1 (sp - 16) 8 (U (getr regs 8))) by zcell;
    assert (F9 : cellA X1 (sp - 24) 8 (U (getr regs 9))) by zcell; assert (F18 : cellA X1 (sp - 32) 8 (U (getr regs 18))) by zcell;
    assert (Wlk1 : wokA X1 (0x13e3d8 + 616) 1) by zwok;
    destruct (art_gbb_loop chs R1 X1 rom parr (parr + Z.of_nat (length chs) * 2 ^ 3) m 0 ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rwH; reflexivity) ltac:(gres; reflexivity)
                ltac:(lia) Hn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cws1) as (r2 & RUN2 & Q13 & K2);
    gkeep K2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -32)); gkeep K2 r2 (8%bv : reg) (Z_to_bv 64 (0x13e3d8 + 616)); gkeep K2 r2 (10%bv : reg) (Z_to_bv 64 0x13e3d8);
    gkeep K2 r2 (11%bv : reg) (Z_to_bv 64 m)
  end.
  rewrite <- Eh in Q13.
  match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
  {
    zbft F_553a8 D_553a8.
    zld F_553ac D_553ac h Cmb1.
    zbft F_553b0 D_553b0.
    zld F_553b4 D_553b4 (h + 8) Cms1.
    zstep F_553b8 D_553b8.
    zbft F_553bc D_553bc. zbft F_553c0 D_553c0. zbft F_553c4 D_553c4.
    zld F_553c8 D_553c8 0x13e3d8 Cpg1.
    zstep F_553cc D_553cc.
    stepn F_553d0 D_553d0. rwH. rewrite art_zb_and by lia.
    replace (Z.land 4095 h) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; lia).
    zbft F_553d4 D_553d4.
    zstep F_553d8 D_553d8.
    stepn F_553dc D_553dc.
    stepfence F_55404 D_55404.
    zsb F_55408 D_55408 (0x13e3d8 + 616) 0 ltac:(exact Wlk1).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
       assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell end.
    zld F_5540c D_5540c (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
    zld F_55410 D_55410 (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_55414 D_55414 (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
    zld F_55418 D_55418 (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
    zstep F_5541c D_5541c.
    stepret F_55420 D_55420 raw ltac:(reflexivity).
    apply mst_refl. }
  eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|].
  destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|].
  repeat (destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_gbb_mem_facts : forall M sp raw regs, 0x698000 + 32 <= sp -> sp < 2 ^ 64 ->
  let M' := art_gbb_mem M sp raw regs in
  mem_grows M M' /\ art_agree [(sp - 32, 32); (0x13e3d8 + 616, 4)] M M' /\ cellA M' (0x13e3d8 + 616) 4 0.
Proof.
  intros M sp raw regs Hsp Hsp'. cbv zeta. unfold art_gbb_mem, art_flush_frame. split; [zgrows|]. split.
  - eapply art_agree_sub; [zagree|]. zsub.
  - apply art_lock_word_release; [lia|lia|]. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End FPX2.
