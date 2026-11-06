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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison EbtSecAlloc ArtRuns ArtRunsMem EbtFp EbtCellEx EbtImgCell EbtSecRSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c Eb0_code_r5f7d0_5f958 Eb0_code_r7add0_7ae74 Eb0_code_r719f8_71a24.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_m2s_lo_fn : forall regs (M rom : word -> option byte) (raw : word) (a : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 a -> 0 <= a <= SB - 1 -> art_layout M ->
  msteps ASEGS (mkst regs (0x7a718 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (2147450880 + a / 8))) 11 (Z_to_bv 64 2147450880)) 12 (Z_to_bv 64 2147450879)) 13 (Z_to_bv 64 2147450879)) raw M rom).
Proof.
  intros regs M rom raw a H1 Hret H10 Ha L. unfold SB in *.
  destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  stepn F_7a6c8 D_7a6c8.
  zld F_7a6cc D_7a6cc 0x13d8c8 L1.
  zld F_7a6d0 D_7a6d0 0x1460f8 L2.
  zstep F_7a6d4 D_7a6d4. zstep F_7a6d8 D_7a6d8. zstep F_7a6dc D_7a6dc.
  stepn F_7a6e0 D_7a6e0. rwH. zclosed 2147450879.
  zbtk F_7a6e4 D_7a6e4.
  stepn F_7a728 D_7a728. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_7a72c D_7a72c.
  stepret F_7a730 D_7a730 raw ltac:(rwH; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_m2s_hi_fn : forall regs (M rom : word -> option byte) (raw : word) (a : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 a -> kHighMemBeg <= a <= kHighMemEnd -> art_layout M ->
  msteps ASEGS (mkst regs (0x7a718 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 5 (Z_to_bv 64 140737488355327)) 10 (Z_to_bv 64 (2147450880 + a / 8))) 11 (Z_to_bv 64 2147450880)) 12 (Z_to_bv 64 2147450879)) 13 (Z_to_bv 64 0)) 14 (Z_to_bv 64 17592186044415)) 15 (Z_to_bv 64 18446744073709551615)) 16 (Z_to_bv 64 0)) 17 (Z_to_bv 64 17594333495295)) raw M rom).
Proof.
  intros regs M rom raw a H1 Hret H10 Ha L. unfold SB, kHighMemBeg, kHighMemEnd in *.
  destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
  stepn F_7a6c8 D_7a6c8.
  zld F_7a6cc D_7a6cc 0x13d8c8 L1.
  zld F_7a6d0 D_7a6d0 0x1460f8 L2.
  zstep F_7a6d4 D_7a6d4. zstep F_7a6d8 D_7a6d8. zstep F_7a6dc D_7a6dc.
  stepn F_7a6e0 D_7a6e0. rwH. zclosed 2147450879.
  zbft F_7a6e4 D_7a6e4.
  stepn F_7a6e8 D_7a6e8.
  zld F_7a6ec D_7a6ec 0x13d8d0 L3.
  stepn F_7a6f0 D_7a6f0.
  zld F_7a6f4 D_7a6f4 0x13d8d8 L5.
  zld F_7a6f8 D_7a6f8 0x146de8 L4.
  zld F_7a6fc D_7a6fc 0x146df0 L6.
  zstep F_7a700 D_7a700.
  zbtk F_7a704 D_7a704.
  stepn F_7a70c D_7a70c.
  zld F_7a710 D_7a710 0x13d8e0 L7.
  zld F_7a714 D_7a714 0x146de0 L8.
  stepn F_7a718 D_7a718. rwH. zclosed 17592186044415.
  zstep F_7a71c D_7a71c.
  zbft F_7a720 D_7a720.
  zbft F_7a724 D_7a724.
  stepn F_7a728 D_7a728. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
  zstep F_7a72c D_7a72c.
  stepret F_7a730 D_7a730 raw ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.

Definition art_pg_dn (x : Z) : Z := x - x mod 4096.
Definition art_flush_beg (mb : Z) : Z := art_pg_dn (SB + mb / 8 + 4095).
Definition art_flush_end (mb ms : Z) : Z := art_pg_dn (SB + (mb + ms) / 8).

Definition art_flush_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)).

Section FPX1. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_layout_flush_frame : forall M sp raw regs, 0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> art_layout M -> art_layout (art_flush_frame M sp raw regs).
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
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> 0 <= mb /\ mb + ms <= SB - 1 -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x7a6cc : word) M rom) (mkst regs' (0x96228 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + mb / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (mb + ms) / 8)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
  pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
  eexists. split.
  {
  zstep F_7a67c D_7a67c.
  zsd F_7a680 D_7a680 (sp - 8) (U raw) ltac:(rewok W). zsd F_7a684 D_7a684 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7a688 D_7a688 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7a68c D_7a68c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_7a690 D_7a690. zstep F_7a694 D_7a694.
  stepn F_7a698 D_7a698.
  change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
  pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
  zcall (art_m2s_lo_fn _ _ _ (0x7a6ec : word) mb).
  zstep F_7a69c D_7a69c. zstep F_7a6a0 D_7a6a0.
  stepn F_7a6a4 D_7a6a4.
  zcall (art_m2s_lo_fn _ _ _ (0x7a6f8 : word) (ms + mb)).
  zstep F_7a6a8 D_7a6a8. zstep F_7a6ac D_7a6ac.
  destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  zld F_7a6b0 D_7a6b0 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6b4 D_7a6b4 (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6b8 D_7a6b8 (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6bc D_7a6bc (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
  zstep F_7a6c0 D_7a6c0.
  stepn F_7a6c4 D_7a6c4.
  apply mst_refl. }
  replace (mb + ms) with (ms + mb) by lia.
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_flush_a_hi : forall regs (M rom : word -> option byte) (raw : word) (sp mb ms : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 mb -> getr regs 11 = Z_to_bv 64 ms ->
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> kHighMemBeg <= mb /\ mb + ms <= kHighMemEnd -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x7a6cc : word) M rom) (mkst regs' (0x96228 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (SB + mb / 8) /\ getr regs' 11 = Z_to_bv 64 (SB + (mb + ms) / 8)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
  pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
  eexists. split.
  {
  zstep F_7a67c D_7a67c.
  zsd F_7a680 D_7a680 (sp - 8) (U raw) ltac:(rewok W). zsd F_7a684 D_7a684 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_7a688 D_7a688 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7a68c D_7a68c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_7a690 D_7a690. zstep F_7a694 D_7a694.
  stepn F_7a698 D_7a698.
  change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
  pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
  zcall (art_m2s_hi_fn _ _ _ (0x7a6ec : word) mb).
  zstep F_7a69c D_7a69c. zstep F_7a6a0 D_7a6a0.
  stepn F_7a6a4 D_7a6a4.
  zcall (art_m2s_hi_fn _ _ _ (0x7a6f8 : word) (ms + mb)).
  zstep F_7a6a8 D_7a6a8. zstep F_7a6ac D_7a6ac.
  destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  zld F_7a6b0 D_7a6b0 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6b4 D_7a6b4 (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6b8 D_7a6b8 (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
  zld F_7a6bc D_7a6bc (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
  zstep F_7a6c0 D_7a6c0.
  stepn F_7a6c4 D_7a6c4.
  apply mst_refl. }
  replace (mb + ms) with (ms + mb) by lia.
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

Definition art_rel_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte := art_flush_frame M sp raw regs.

#[using="Type"] Lemma art_rel_head : forall regs (M rom : word -> option byte) (raw : word) (sp sa sb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 sb ->
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 -> 0 <= sa -> sa + 4096 < 2 ^ 64 -> 0 <= sb < 2 ^ 64 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  exists regs', msteps ASEGS (mkst regs (0x96228 : word) M rom) (mkst regs' (0x96280 : word) (art_flush_frame M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (art_pg_dn (sa + 4095)) /\ getr regs' 11 = Z_to_bv 64 (art_pg_dn sb)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 32)
    /\ (forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp sa sb H1 H2 H10 H11 Hsp Hsp' W Hsa Hsa' Hsb Cpc Cpg.
  eexists. split.
  {
  zstep F_961d8 D_961d8.
  zsd F_961dc D_961dc (sp - 8) (U raw) ltac:(rewok W).
  zsd F_961e0 D_961e0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_961e4 D_961e4 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_961e8 D_961e8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zstep F_961ec D_961ec.
  stepn F_961f0 D_961f0.
  match goal with |- msteps _ (mkst _ _ ?Y _) _ => assert (Cpc2 : cellA Y 0x13d8a8 8 0x1d5ba0) by zcell; assert (Cpg2 : cellA Y 0x1d5ba0 8 4096) by zcell end.
  zld F_961f4 D_961f4 0x13d8a8 Cpc2.
  zld F_961f8 D_961f8 0x1d5ba0 Cpg2.
  zstep F_961fc D_961fc.
  zbtk F_96200 D_96200.
  zstep F_96210 D_96210.
  stepn F_96214 D_96214. rwH. zclosed 0.
  zbft F_96218 D_96218.
  zstep F_9621c D_9621c.
  stepn F_96220 D_96220. rwH. zclosed 18446744073709547520.
  zstep F_96224 D_96224.
  replace (sa + 4096 + -1) with (sa + 4095) by lia.
  stepn F_96228 D_96228. rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  stepn F_9622c D_9622c. rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  unfold art_flush_frame. apply mst_refl. }
  unfold art_pg_dn.
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_rel_madv : forall regs (M rom : word -> option byte) (raw : word) (sp beg en x8 x9 x18 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 en ->
  32 <= sp -> sp < 2 ^ 64 -> 0 <= beg -> beg < en -> en < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M 0x13d908 8 1 ->
  msteps ASEGS (mkst regs (0x96280 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 (en - beg))) 12 (Z_to_bv 64 4)) 13 (Z_to_bv 64 4)) 17 (Z_to_bv 64 233)) 18 (Z_to_bv 64 x18))
      (0x8ce70 : word) M rom).
Proof.
  intros regs M rom raw sp beg en x8 x9 x18 H2 H10 H11 Hsp Hsp' Hb Hbe He Hx8 Hx9 Hx18 F1 F8 F9 F18 Cgot.
  zbft F_96230 D_96230.
  zstep F_96234 D_96234. zstep F_96238 D_96238.
  zld F_9623c D_9623c (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_96240 D_96240 (sp - 16) F8.
  zld F_96244 D_96244 (sp - 24) F9.
  zld F_96248 D_96248 (sp - 32) F18.
  zstep F_9624c D_9624c.
  stepn F_96250 D_96250.
  stepn F_8ce00 D_8ce00.
  zld F_8ce04 D_8ce04 0x13d908 Cgot.
  zbft F_8ce08 D_8ce08.
  zstep F_8ce0c D_8ce0c.
  zbtk F_8ce10 D_8ce10.
  zstep F_8ce1c D_8ce1c.
  zret.
Qed.

#[using="Type"] Lemma art_rel_skip : forall regs (M rom : word -> option byte) (raw : word) (sp beg en x8 x9 x18 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 10 = Z_to_bv 64 beg -> getr regs 11 = Z_to_bv 64 en -> ret_ok raw ->
  32 <= sp -> sp < 2 ^ 64 -> 0 <= en -> en <= beg -> beg < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  msteps ASEGS (mkst regs (0x96280 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 18 (Z_to_bv 64 x18)) raw M rom).
Proof.
  intros regs M rom raw sp beg en x8 x9 x18 H2 H10 H11 Hret Hsp Hsp' He Hbe Hb Hx8 Hx9 Hx18 F1 F8 F9 F18.
  zbtk F_96230 D_96230.
  zld F_96254 D_96254 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_96258 D_96258 (sp - 16) F8.
  zld F_9625c D_9625c (sp - 24) F9.
  zld F_96260 D_96260 (sp - 32) F18.
  zstep F_96264 D_96264.
  stepret F_96268 D_96268 raw ltac:(reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_flush_post_fn : forall regs (M rom : word -> option byte) (raw : word),
  getr regs 1 = raw -> ret_ok raw -> getr regs 10 = Z_to_bv 64 0 ->
  msteps ASEGS (mkst regs (0x8ce74 : word) M rom) (mkst (regupd regs 10 (Z_to_bv 64 0)) raw M rom).
Proof.
  intros regs M rom raw H1 Hret H10.
  stepn F_8ce24 D_8ce24. rwH. zclosed 0.
  stepret F_8ce28 D_8ce28 raw ltac:(rwH; reflexivity).
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
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M ->
  exists regs', msteps ASEGS (mkst regs (0x7a6cc : word) M rom) (mkst regs' (0x96228 : word) (art_flush_frame M sp raw regs) rom)
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
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 -> cellA M 0x13d908 8 1 ->
  art_flush_beg mb < art_flush_end mb ms ->
  exists regs', msteps ASEGS (mkst regs (0x7a6cc : word) M rom) (mkst regs' (0x8ce70 : word) (art_flush_mem M sp raw regs) rom)
    /\ art_madvise_args regs' (art_flush_beg mb) (art_flush_end mb ms - art_flush_beg mb)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Cgot Hbe.
  destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
  destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
  pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
  pose proof (art_flush_frame_other M sp raw regs 0x13d8a8 8%nat 0x1d5ba0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
  pose proof (art_flush_frame_other M sp raw regs 0x1d5ba0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
  pose proof (art_flush_frame_other M sp raw regs 0x13d908 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot) as Cgot1.
  remember (art_flush_frame M sp raw regs) as M1 eqn:EM1.
  destruct (art_rel_head r1 M1 rom raw sp (SB + mb / 8) (SB + (mb + ms) / 8) A1 A2 A10 A11 Hsp Hsp' W1 ltac:(lia) ltac:(lia) ltac:(lia) Cpc1 Cpg1)
    as (r2 & RUN2 & B10 & B11 & B2 & BK).
  rewrite (art_flush_frame_ext M1 sp raw regs r1 (AK 8%bv ltac:(cbn; tauto)) (AK 9%bv ltac:(cbn; tauto)) (AK 18%bv ltac:(cbn; tauto))) in RUN2.
  destruct (art_flush_frame_cells M1 sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
  pose proof (art_flush_frame_other M1 sp raw regs 0x13d908 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot1) as Cgot2.
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
  0x69c000 + 32 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0 <= ms -> art_blk_ok mb ms -> art_layout M -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  art_flush_end mb ms <= art_flush_beg mb ->
  exists regs', msteps ASEGS (mkst regs (0x7a6cc : word) M rom) (mkst regs' raw (art_flush_mem M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp mb ms H1 Hret H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Hbe.
  destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
  destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
  pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
  pose proof (art_flush_frame_other M sp raw regs 0x13d8a8 8%nat 0x1d5ba0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
  pose proof (art_flush_frame_other M sp raw regs 0x1d5ba0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
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
    msteps ASEGS (mkst regs (0x55bf4 : word) M rom) (mkst regs' (0x55c20 : word) M rom)
    /\ getr regs' 13 = Z_to_bv 64 (art_gbb_scan m near chs)
    /\ (forall r : reg, r <> 5%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
  induction chs as [|ch chs IH]; intros regs M rom cur en m near H12 H14 H11 H13 Een Hlen Hcur Hen Hnear Hm Cws; cbn [length] in *. lia.
  destruct (Cws O ltac:(lia)) as [Rch Cch]. cbn [nth] in Rch, Cch. replace (cur + 8 * Z.of_nat 0) with cur in Cch by lia.
  set (near' := if (ch <=? m) && (near <? ch) then ch else near).
  assert (Hnear' : 0 <= near' <= m) by (subst near'; destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia).
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x55bf4 : word) M rom) (mkst regs1 (0x55bf0 : word) M rom)
            /\ getr regs1 12 = Z_to_bv 64 (cur + 8) /\ getr regs1 13 = Z_to_bv 64 near' /\ getr regs1 14 = Z_to_bv 64 en /\ getr regs1 11 = Z_to_bv 64 m
            /\ (forall r : reg, r <> 5%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)).
  { destruct (Z.leb_spec ch m) as [Lm|Gm].
    - destruct (Z.ltb_spec near ch) as [Ln|Gn]; subst near'; cbn [andb].
      +
        eexists. split.
        { zld F_55ba4 D_55ba4 cur Cch. zstep F_55ba8 D_55ba8. zstep F_55bac D_55bac. zstep F_55bb0 D_55bb0.
          zbtk F_55bb4 D_55bb4. zbft F_55bc4 D_55bc4. zstep F_55bc8 D_55bc8. stepn F_55bcc D_55bcc. zstep F_55b9c D_55b9c. apply mst_refl. }
        repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
      +
        eexists. split.
        { zld F_55ba4 D_55ba4 cur Cch. zstep F_55ba8 D_55ba8. zstep F_55bac D_55bac. zstep F_55bb0 D_55bb0.
          zbft F_55bb4 D_55bb4. zstep F_55bb8 D_55bb8. zbft F_55bbc D_55bbc. stepn F_55bc0 D_55bc0. zstep F_55bc8 D_55bc8. stepn F_55bcc D_55bcc. zstep F_55b9c D_55b9c. apply mst_refl. }
        repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
    -
      subst near'. cbn [andb].
      eexists. split.
      { zld F_55ba4 D_55ba4 cur Cch. zstep F_55ba8 D_55ba8. zstep F_55bac D_55bac. zstep F_55bb0 D_55bb0.
        replace (Z_to_bv 64 (m - ch)) with (Z_to_bv 64 (2 ^ 64 + m - ch)) by (apply art_zb_eq; replace (2 ^ 64 + m - ch) with (m - ch + 1 * 2 ^ 64) by lia; apply Z_mod_plus_full).
        zbft F_55bb4 D_55bb4. zstep F_55bb8 D_55bb8. zbtk F_55bbc D_55bbc. zstep F_55b9c D_55b9c. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P12 & P13 & P14 & P11 & K1).
  destruct chs as [|ch2 chs2].
  -
    cbn [length] in *. eexists. split; [|split].
    + eapply msteps_trans; [exact RUN1|]. zbtk F_55ba0 D_55ba0. apply mst_refl.
    + cbn [art_gbb_scan]. exact P13.
    + exact K1.
  - cbn [length] in *.
    assert (RUNb : msteps ASEGS (mkst regs1 (0x55bf0 : word) M rom) (mkst regs1 (0x55bf4 : word) M rom)).
    { zbft F_55ba0 D_55ba0. apply mst_refl. }
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
  Wn 1 (Wn 4 (art_flush_frame M sp raw regs) (0x142ad8 + 616) 1) (0x142ad8 + 616) 0.

Ltac gkeep K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).

#[using="Type"] Lemma art_gbb_run : forall chs regs (M rom : word -> option byte) (raw : word) (sp HI m parr h mbeg msz : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x142ad8 -> getr regs 11 = Z_to_bv 64 m ->
  0x69c000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  (1 <= length chs)%nat -> Z.of_nat (length chs) < 2 ^ 20 -> 0x69c000 <= parr -> parr + 8 * Z.of_nat (length chs) <= HI -> 0 <= m < 2 ^ 64 ->
  cellA M (0x142ad8 + 616) 4 0 -> cellA M (0x142ad8 + 56) 8 (Z.of_nat (length chs)) -> cellA M (0x142ad8 + 8) 8 parr -> cellA M 0x142ad8 8 4096 ->
  (forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA M (parr + 8 * Z.of_nat j) 8 (nth j chs 0)) ->
  h = art_gbb_scan m 0 chs -> 0x69c000 <= h -> h + 16 <= HI -> h mod 4096 = 0 ->
  cellA M h 8 mbeg -> cellA M (h + 8) 8 msz -> 0 <= mbeg <= h -> h < mbeg + msz -> m < mbeg + msz -> 0 <= msz -> mbeg + msz < 2 ^ 64 ->
  exists regs', msteps ASEGS (mkst regs (0x55b88 : word) M rom) (mkst regs' raw (art_gbb_mem M sp raw regs) rom)
    /\ getr regs' 10 = Z_to_bv 64 (h + 4096) /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros chs regs M rom raw sp HI m parr h mbeg msz H1 Hret H2 H10 H11 HHI Hsp Hsp' W Hn Hn' Hparr Hparr' Hm Clk Cn Cparr Cpg Cws Eh Hh Hh' Hh4 Cmb Cms Hmb Hhm Hmm Hms Hme.
  assert (Hhr : 0 <= h <= m) by (rewrite Eh; apply art_gbb_scan_range; [lia|]; apply Forall_forall; intros x Hx; destruct (In_nth _ _ 0 Hx) as (j & Hj & <-); apply (Cws j Hj)).
  pose proof (art_img_wr M (0x142ad8 + 616) 4 ltac:(lia) ltac:(lia) ltac:(lia)) as Wlk.
  eassert (RUN1 : msteps ASEGS (mkst regs (0x55b88 : word) M rom) _).
  {
    zstep F_55b38 D_55b38.
    zsd F_55b3c D_55b3c (sp - 8) (U raw) ltac:(rewok W). zsd F_55b40 D_55b40 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_55b44 D_55b44 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55b48 D_55b48 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zstep F_55b4c D_55b4c. zstep F_55b50 D_55b50.
    stepn F_55b54 D_55b54. rwH. zclosed (0x142ad8 + 616).
    zstep F_55b58 D_55b58.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x142ad8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x142ad8 + 616) 4) by zwok end.
    zcas6 F_55b5c D_55b5c F_55b60 D_55b60 F_55b64 D_55b64 F_55b68 D_55b68 F_55b6c D_55b6c F_55b70 D_55b70 (0x142ad8 + 616) 0 1 1 1 Clk' Wlk'.
    zbft F_55b74 D_55b74.
    stepn F_55b78 D_55b78. rwH. zclosed 0.
    zbft F_55b7c D_55b7c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cn' : cellA X (0x142ad8 + 56) 8 (Z.of_nat (length chs))) by zcell; assert (Cparr' : cellA X (0x142ad8 + 8) 8 parr) by zcell end.
    zld F_55b80 D_55b80 (0x142ad8 + 56) Cn'.
    zbft F_55b84 D_55b84.
    zstep F_55b88 D_55b88.
    zld F_55b8c D_55b8c (0x142ad8 + 8) Cparr'.
    zstep F_55b90 D_55b90. zstep F_55b94 D_55b94.
    stepn F_55b98 D_55b98.
    apply mst_refl. }
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (Cws1 : forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA X1 (parr + 8 * Z.of_nat j) 8 (nth j chs 0))
      by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
    assert (Cmb1 : cellA X1 h 8 mbeg) by zcell; assert (Cms1 : cellA X1 (h + 8) 8 msz) by zcell; assert (Cpg1 : cellA X1 0x142ad8 8 4096) by zcell;
    assert (F1 : cellA X1 (sp - 8) 8 (U raw)) by zcell; assert (F8 : cellA X1 (sp - 16) 8 (U (getr regs 8))) by zcell;
    assert (F9 : cellA X1 (sp - 24) 8 (U (getr regs 9))) by zcell; assert (F18 : cellA X1 (sp - 32) 8 (U (getr regs 18))) by zcell;
    assert (Wlk1 : wokA X1 (0x142ad8 + 616) 1) by zwok;
    destruct (art_gbb_loop chs R1 X1 rom parr (parr + Z.of_nat (length chs) * 2 ^ 3) m 0 ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rwH; reflexivity) ltac:(gres; reflexivity)
                ltac:(lia) Hn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cws1) as (r2 & RUN2 & Q13 & K2);
    gkeep K2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -32)); gkeep K2 r2 (8%bv : reg) (Z_to_bv 64 (0x142ad8 + 616)); gkeep K2 r2 (10%bv : reg) (Z_to_bv 64 0x142ad8);
    gkeep K2 r2 (11%bv : reg) (Z_to_bv 64 m)
  end.
  rewrite <- Eh in Q13.
  match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
  {
    zbft F_55bd0 D_55bd0.
    zld F_55bd4 D_55bd4 h Cmb1.
    zbft F_55bd8 D_55bd8.
    zld F_55bdc D_55bdc (h + 8) Cms1.
    zstep F_55be0 D_55be0.
    zbft F_55be4 D_55be4. zbft F_55be8 D_55be8. zbft F_55bec D_55bec.
    zld F_55bf0 D_55bf0 0x142ad8 Cpg1.
    zstep F_55bf4 D_55bf4.
    stepn F_55bf8 D_55bf8. rwH. rewrite art_zb_and by lia.
    replace (Z.land 4095 h) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; lia).
    zbft F_55bfc D_55bfc.
    zstep F_55c00 D_55c00.
    stepn F_55c04 D_55c04.
    stepfence F_55c2c D_55c2c.
    zsb F_55c30 D_55c30 (0x142ad8 + 616) 0 ltac:(exact Wlk1).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
       assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell end.
    zld F_55c34 D_55c34 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
    zld F_55c38 D_55c38 (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
    zld F_55c3c D_55c3c (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
    zld F_55c40 D_55c40 (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
    zstep F_55c44 D_55c44.
    stepret F_55c48 D_55c48 raw ltac:(reflexivity).
    apply mst_refl. }
  eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|].
  destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|].
  repeat (destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_gbb_mem_facts : forall M sp raw regs, 0x69c000 + 32 <= sp -> sp < 2 ^ 64 ->
  let M' := art_gbb_mem M sp raw regs in
  mem_grows M M' /\ art_agree [(sp - 32, 32); (0x142ad8 + 616, 4)] M M' /\ cellA M' (0x142ad8 + 616) 4 0.
Proof.
  intros M sp raw regs Hsp Hsp'. cbv zeta. unfold art_gbb_mem, art_flush_frame. split; [zgrows|]. split.
  - eapply art_agree_sub; [zagree|]. zsub.
  - apply art_lock_word_release; [lia|lia|]. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End FPX2.
