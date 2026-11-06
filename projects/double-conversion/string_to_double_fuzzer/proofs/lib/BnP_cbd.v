(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_au64 BnP_mul2 BnP_ads2 BnP_ads5 BnCbdLib.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition CSX : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Ltac regeq H := first [exact H | etransitivity; [exact H|]; f_equal; lia].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma cbd_p1_P : forall regs m (S buf len expo a4 : Z) (ret f : word) (ds : list Z),
  getr regs 2%bv = Z_to_bv 64 S -> getr regs 10%bv = Z_to_bv 64 buf -> getr regs 11%bv = Z_to_bv 64 len ->
  getr regs 12%bv = Z_to_bv 64 expo -> getr regs 13%bv = f -> getr regs 14%bv = Z_to_bv 64 a4 -> getr regs 1%bv = ret ->
  zlen ds = len -> 1 <= len <= 780 -> digits_ok ds -> digs m buf ds ->
  arr32 SEGS_P m 80520 five_tbl ->
  1 <= buf -> buf + len < 2 ^ 62 -> 82456 <= S -> S < 2 ^ 62 -> (S <= buf \/ buf + len <= S - 1888) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 (S - 1888)) 1888 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35320) m rom) (mkst regs' (Z_to_bv 64 0x35364) m' rom)
    /\ bn_at SEGS_P m' (S - 548) (assign_decimal ds) /\ bn_at SEGS_P m' (S - 1064) (assign_u64 (bv_unsigned f))
    /\ getr regs' 2%bv = Z_to_bv 64 (S - 1072) /\ getr regs' 8%bv = Z_to_bv 64 a4 /\ getr regs' 9%bv = Z_to_bv 64 expo
    /\ keeps CSX regs regs'
    /\ cellN SEGS_P m' (S - 8) 8 (bv_unsigned ret) /\ cellN SEGS_P m' (S - 16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_P m' (S - 24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_P m' (S - 32) 8 (bv_unsigned (getr regs 18%bv))
    /\ arr32 SEGS_P m' 80520 five_tbl
    /\ unch m m' [(S - 1888, S)] /\ mem_grows m m'.
Proof.
  intros regs m S buf len expo a4 ret f ds R2 R10 R11 R12 R13 R14 R1 Hzl Hlen Hdok Hdigs Htbl Hb1 Hb2 HS1 HS2 Hdisj Hsto.
  pose proof (u64_range ret) as W1. pose proof (u64_range f) as Wf. pose proof (u64_range (getr regs 8%bv)) as W8.
  pose proof (u64_range (getr regs 9%bv)) as W9. pose proof (u64_range (getr regs 18%bv)) as W18.
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 780); None; Some (0, 2 ^ 64 - 1); None]) (@nil kcell) [KW (ZV 32) (-1888) 0])
    40%nat [0x35704] (SCR [] [])
    constr:([(2%bv : reg, ZV 32); (10%bv : reg, ZV 33); (11%bv : reg, ZV 34); (12%bv : reg, ZV 35); (13%bv : reg, ZV 36); (14%bv : reg, ZV 37)])
    [S; buf; len; expo; bv_unsigned f; a4]
    constr:([Some (82456, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 780); @None (Z * Z); Some (0, 2 ^ 64 - 1); @None (Z * Z)]) regs m rom 0x35320.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(exact I). zx_name regs1.
  set (m1 := wbytes _ _ _) in ZM.
  assert (U01 : unch m m1 [(S - 1888, S)]) by (unfold m1; unchx).
  assert (G01 : mem_grows m m1) by (unfold m1; growsx).
  assert (SAV : cellN SEGS_P m1 (S - 8) 8 (bv_unsigned ret) /\ cellN SEGS_P m1 (S - 16) 8 (bv_unsigned (getr regs 8%bv))
    /\ cellN SEGS_P m1 (S - 24) 8 (bv_unsigned (getr regs 9%bv)) /\ cellN SEGS_P m1 (S - 32) 8 (bv_unsigned (getr regs 18%bv))
    /\ cellN SEGS_P m1 (S - 548) 2 0 /\ cellN SEGS_P m1 (S - 548 + 2) 2 0
    /\ cellN SEGS_P m1 (S - 1064) 2 0 /\ cellN SEGS_P m1 (S - 1064 + 2) 2 0).
  { clear ZE ZR ZF ZM Hdisj Hsto Hdigs Htbl U01 G01. unfold m1. pose proof (u64_range (getr regs 1%bv)). rewrite <- R1.
    replace (S - 548) with (S + -548) by lia. replace (S - 1064) with (S + -1064) by lia.
    split; [cellx|]. split; [cellx|]. split; [cellx|]. split; [cellx|].
    split; [apply cellN_store_skip; [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia |]; apply (proj1 (bn_ctor_store SEGS_P _ (S + -548) ltac:(lia) ltac:(lia)))|].
    split; [apply cellN_store_skip; [lia | zwidth; lia | lia | zwidth; lia | zwidth; lia |]; apply (proj2 (bn_ctor_store SEGS_P _ (S + -548) ltac:(lia) ltac:(lia)))|].
    split; [apply (proj1 (bn_ctor_store SEGS_P _ (S + -1064) ltac:(lia) ltac:(lia)))|].
    apply (proj2 (bn_ctor_store SEGS_P _ (S + -1064) ltac:(lia) ltac:(lia))). }
  destruct SAV as (S1 & S2 & S3 & S4 & C1 & C2 & C3 & C4).
  zx_reg ZR (2%bv : reg) as A2. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (12%bv : reg) as A12.
  zx_reg ZR (1%bv : reg) as A1. zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (18%bv : reg) as A18.
  assert (K1 : keeps CSX regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF.
  assert (Hdigs1 : digs m1 buf ds).
  { eapply digs_unch; [exact U01 | lia | rewrite Hzl; lia | | exact Hdigs]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; rewrite Hzl; lia. }
  assert (Htbl1 : arr32 SEGS_P m1 80520 five_tbl).
  { eapply arr32_unch; [exact U01 | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_P m1 (Z_to_bv 64 (S - 1888)) 1888 = true) by (eapply store_ok_grows; [exact G01 | exact Hsto]).
  (* [comment removed for export] *)
  assert (Hret1 : ret_ok (Z_to_bv 64 217944)) by (apply ret_ok_even; reflexivity).
  destruct (ads_P rom regs1 m1 (S - 548) buf len (S - 1072) (Z_to_bv 64 217944) ds) as (regs2 & m2 & M2 & K2 & Hbn2 & Htbl2 & U2 & G2).
  { regeq A10. } { exact A11. } { exact A12. } { regeq A2. } { exact A1. } { exact Hret1. }
  { exact Hzl. } { exact Hlen. } { exact Hdok. } { exact Hdigs1. } { exact Htbl1. }
  { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. } { lia. }
  { eapply sc_store_in; [exact Hsto1 | cbn; lia]. }
  { eapply sc_store_in; [exact Hsto1 | cbn; lia]. }
  assert (U2' : unch m1 m2 [(S - 1888, S - 32)]).
  { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 (S - 1072)) by (etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | regeq A2]).
  assert (B18 : getr regs2 18%bv = f) by (etransitivity; [exact (K2 18 ltac:(cbn; tauto)) |]; etransitivity; [exact A18 | apply Z_to_bv_bv_unsigned]).
  assert (B8 : getr regs2 8%bv = Z_to_bv 64 a4) by (etransitivity; [exact (K2 8 ltac:(cbn; tauto)) | exact A8]).
  assert (B9 : getr regs2 9%bv = Z_to_bv 64 expo) by (etransitivity; [exact (K2 9 ltac:(cbn; tauto)) | exact A9]).
  (* [comment removed for export] *)
  zx_run SEGS_P constr:(CTX (vi_regs ++ [Some (82456, 2 ^ 62); Some (0, 2 ^ 64 - 1)]) (@nil kcell) (@nil kwin))
    10%nat [0x356d0] (SCR [] []) constr:([(2%bv : reg, ZAdd (ZV 32) (ZL (-1072))); (18%bv : reg, ZV 33)])
    [S; bv_unsigned f] constr:([Some (82456, 2 ^ 62); Some (0, 2 ^ 64 - 1)]) regs2 m2 rom 0x35358.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
  zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (11%bv : reg) as D11. zx_reg ZR (1%bv : reg) as D1.
  assert (K3 : keeps CS regs2 regs3) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M3. clear ZE ZR ZF.
  (* [comment removed for export] *)
  assert (Hret2 : ret_ok (Z_to_bv 64 217956)) by (apply ret_ok_even; reflexivity).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_P m2 (Z_to_bv 64 (S - 1064)) 516 = true).
  { eapply sc_store_in; [eapply store_ok_grows; [exact G2 | exact Hsto1] | cbn; lia]. }
  destruct (au64_P regs3 m2 rom (S - 1064) (bv_unsigned f) (Z_to_bv 64 217956) ltac:(regeq D10) D11 D1 Hret2
              ltac:(change M64 with (2 ^ 64); lia) ltac:(lia) ltac:(change M64 with (2 ^ 64); lia) Hsto2)
    as (regs4 & m4 & M4 & K4 & Hbn4 & U4 & G4).
  eexists regs4, m4. split.
  { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3 | exact M4]. }
  assert (SAVm : forall a n v, cellN SEGS_P m1 a n v -> 0 <= a -> S - 32 <= a -> a + Z.of_nat n <= S -> (n <= 8)%nat -> cellN SEGS_P m4 a n v).
  { intros a n v C Ha0 Ha1 Ha2 Hn. eapply cellN_unch; [exact U4 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia |].
    eapply cellN_unch; [exact U2' | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact C]. }
  split.
  { eapply bn_at_unch; [exact U4 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Hbn2]. }
  split; [exact Hbn4|].
  split; [etransitivity; [exact (K4 2 ltac:(cbn; tauto)) |]; etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact B2]|].
  split; [etransitivity; [exact (K4 8 ltac:(cbn; tauto)) |]; etransitivity; [exact (K3 8 ltac:(cbn; tauto)) | exact B8]|].
  split; [etransitivity; [exact (K4 9 ltac:(cbn; tauto)) |]; etransitivity; [exact (K3 9 ltac:(cbn; tauto)) | exact B9]|].
  split.
  { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
  split; [apply SAVm; [exact S1 | lia | lia | zwidth; lia | lia]|].
  split; [apply SAVm; [exact S2 | lia | lia | zwidth; lia | lia]|].
  split; [apply SAVm; [exact S3 | lia | lia | zwidth; lia | lia]|].
  split; [apply SAVm; [exact S4 | lia | lia | zwidth; lia | lia]|].
  split.
  { eapply arr32_unch; [exact U4 | lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Htbl2]. }
  split.
  { eapply unch_trans; [exact U01|]. eapply unch_trans.
    - eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]).
    - eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G2 | exact G4].
Qed.

End S.
