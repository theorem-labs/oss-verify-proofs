(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison ArtAllocG ArtUnwind ArtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_5fc54_604d4 As0_code_67d5c_67ecc As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_land15_mod16 : forall n, 0 <= n -> n mod 16 = 0 -> Z.land n 15 = 0.
Proof. intros n Hn H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_icu1_16 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 16 -> getr regs 11 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x633000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x633000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x633000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x633000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0xde818 1 1 -> cellA M 0xde83c 4 30 -> cellA M 0xd58a8 8 0x16f668 -> cellA M (0x16f668 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x603a0 : word) M rom) (mkst regs1 (0x80834 : word) M1 rom)
    /\ getr regs1 1 = (0x67e98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2224) /\ getr regs1 10 = Z_to_bv 64 (S - 2136)
    /\ getr regs1 11 = Z_to_bv 64 0x60438 /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2288 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21)) /\ cellA M1 (S - 64) 8 (U (getr regs 22))
    /\ cellA M1 (S - 2152) 8 0x60494 /\ cellA M1 (S - 2160) 8 S /\ cellA M1 (S - 2168) 8 n /\ cellA M1 (S - 2176) 8 16 /\ cellA M1 (S - 2184) 8 (U (0x60438 : bv 64)%bv)
    /\ cellA M1 (S - 2192) 8 1 /\ cellA M1 (S - 2200) 8 (S - 2136) /\ cellA M1 (S - 2208) 8 (S - 89)
    /\ cellA M1 (S - 2216) 8 (U (getr regs 23)) /\ cellA M1 (S - 2224) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2136) 8 (S - 2120) /\ cellA M1 (S - 2128) 4 0 /\ cellA M1 (S - 2124) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_603a0 D_603a0.
    zsd F_603a4 D_603a4 (S - 8) (U raw0) ltac:(rewok W). zsd F_603a8 D_603a8 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_603ac D_603ac (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_603b0 D_603b0 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_603b4 D_603b4 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_603b8 D_603b8 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_603bc D_603bc (S - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_603c0 D_603c0 (S - 64) (U (getr regs 22)) ltac:(rewok W).
    zstep F_603c4 D_603c4. zstep F_603c8 D_603c8. zstep F_603cc D_603cc. zstep F_603d0 D_603d0. zstep F_603d4 D_603d4.
    zstep F_603d8 D_603d8. zstep F_603dc D_603dc. zstep F_603e0 D_603e0. zstep F_603e4 D_603e4. zstep F_603e8 D_603e8.
    zsd F_603ec D_603ec (S - 80) 0 ltac:(rewok W).
    zsd F_603f0 D_603f0 (S - 2136) (S - 2120) ltac:(rewok W).
    zsd F_603f4 D_603f4 (S - 2128) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2128)) by lia. replace (S - 2128 + 4) with (S - 2124) by lia.
    stepn F_603f8 D_603f8.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_603fc D_603fc.
    zbtk F_60400 D_60400.
    stepn F_60434 D_60434.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_60438 D_60438.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0xd58a8 8 0x16f668) by zcell; assert (Cfast' : cellA X (0x16f668 + 34) 1 1) by zcell end.
    zld F_6043c D_6043c 0xd58a8 Cg38'. zlbu F_60440 D_60440 (0x16f668 + 34) Cfast'.
    zstep F_60444 D_60444.
    stepn F_60448 D_60448.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_6044c D_6044c. zstep F_60450 D_60450. zstep F_60454 D_60454.
    stepn F_60458 D_60458. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_6045c D_6045c.
    zsd F_60460 D_60460 (S - 80) S ltac:(rewok W).
    zbtk F_60464 D_60464.
    zstep F_60478 D_60478. zstep F_6047c D_6047c. zstep F_60480 D_60480. zstep F_60484 D_60484. zstep F_60488 D_60488. zstep F_6048c D_6048c.
    stepn F_60490 D_60490.
    (* [comment removed for export] *)
    zstep F_67d7c D_67d7c.
    zsd F_67d80 D_67d80 (S - 2152) 0x60494 ltac:(rewok W). zsd F_67d84 D_67d84 (S - 2160) S ltac:(rewok W). zsd F_67d88 D_67d88 (S - 2168) n ltac:(rewok W).
    zsd F_67d8c D_67d8c (S - 2176) 16 ltac:(rewok W). zsd F_67d90 D_67d90 (S - 2184) (U (0x60438 : bv 64)%bv) ltac:(rewok W). zsd F_67d94 D_67d94 (S - 2192) 1 ltac:(rewok W).
    zsd F_67d98 D_67d98 (S - 2200) (S - 2136) ltac:(rewok W). zsd F_67d9c D_67d9c (S - 2208) (S - 89) ltac:(rewok W).
    zsd F_67da0 D_67da0 (S - 2216) (U (getr regs 23)) ltac:(rewok W). zsd F_67da4 D_67da4 (S - 2224) (U (getr regs 24)) ltac:(rewok W).
    zstep F_67da8 D_67da8. zstep F_67dac D_67dac. zstep F_67db0 D_67db0. zstep F_67db4 D_67db4. zstep F_67db8 D_67db8. zstep F_67dbc D_67dbc.
    zsw F_67dc0 D_67dc0 (S - 2128) 0 ltac:(rewok W).
    stepn F_67dc4 D_67dc4.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_67dc8 D_67dc8.
    stepn F_67dcc D_67dcc.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2224) tp key tsd ctx t).
    { unfold art_tsd. repeat split; try lia; zcell. }
    zbft F_67dd0 D_67dd0.
    zstep F_67dd4 D_67dd4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
    zlbu F_67dd8 D_67dd8 (t + 2047 + 1121) Cunw'.
    zstep F_67ddc D_67ddc.
    zsb F_67de0 D_67de0 (t + 2047 + 1121) 1 ltac:(rewok Wt).
    zbft F_67de4 D_67de4.
    zstep F_67de8 D_67de8.
    stepn F_67dec D_67dec.
    zcall (art_stack_top_fn _ _ _ _ t top bot).
    zstep F_67df0 D_67df0. zstep F_67df4 D_67df4.
    stepn F_67df8 D_67df8.
    zcall (art_stack_bottom_fn _ _ _ _ t top bot).
    zstep F_67dfc D_67dfc.
    zbft F_67e00 D_67e00.
    zstep F_67e04 D_67e04. zstep F_67e08 D_67e08. zstep F_67e0c D_67e0c. zstep F_67e10 D_67e10. zstep F_67e14 D_67e14. zstep F_67e18 D_67e18. zstep F_67e1c D_67e1c.
    stepn F_67e20 D_67e20.
    stepn F_67e94 D_67e94.
    zcall (art_unwind_fn _ _ _ _ (S - 2224) (S - 2136) 0x60438 S top bot).
    apply mst_refl.
  - repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
         | |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
         | |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
         | |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
         | |- forall x : word, _ => intros x N1 N2; zagree
         | |- wr _ _ _ _ => zwr
         | |- cell _ _ _ _ _ => zcell
         end.
Qed.

(* [comment removed for export] *)
Lemma art_icu2_16_fn : forall regs (M rom : word -> option byte) (S n t f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2224) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> n mod 16 = 0 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2152) 8 0x60494 -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 -> cellA M (S - 2184) 8 (U (0x60438 : bv 64)%bv) ->
  cellA M (S - 2192) 8 1 -> cellA M (S - 2200) 8 (S - 2136) -> cellA M (S - 2208) 8 (S - 89) -> cellA M (S - 2216) 8 f23 -> cellA M (S - 2224) 8 f24 ->
  msteps ASEGS (mkst regs (0x67e98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3df50 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (S - 2136))) 9 (Z_to_bv 64 16)) 10 (Z_to_bv 64 0xda4d8)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 16)) 13 (Z_to_bv 64 (S - 2136))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 16)) 19 (Z_to_bv 64 (U (0x60438 : bv 64)%bv))) 20 (Z_to_bv 64 1)) 21 (Z_to_bv 64 (S - 2136))) 22 (Z_to_bv 64 (S - 89))) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x3d370 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2152) (U (0x604a8 : bv 64)%bv)) (S - 2160) S) (S - 2168) n) (S - 2176) 16) rom).
Proof.
  intros regs M rom S n t f23 f24 H2 H24 HS HS' Hn Hn16 Ht Ht' Atsp Hf23 Hf24 W Wt C52 C60 C68 C76 C84 C92 C00 C08 C16 C24.
  zsb F_67e98 D_67e98 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D52 : cellA X (S - 2152) 8 0x60494) by zcell; assert (D60 : cellA X (S - 2160) 8 S) by zcell; assert (D68 : cellA X (S - 2168) 8 n) by zcell;
    assert (D76 : cellA X (S - 2176) 8 16) by zcell; assert (D84 : cellA X (S - 2184) 8 (U (0x60438 : bv 64)%bv)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 1) by zcell; assert (D00 : cellA X (S - 2200) 8 (S - 2136)) by zcell;
    assert (D08 : cellA X (S - 2208) 8 (S - 89)) by zcell; assert (D16 : cellA X (S - 2216) 8 f23) by zcell; assert (D24 : cellA X (S - 2224) 8 f24) by zcell end.
  zld F_67e9c D_67e9c (S - 2152) D52. zld F_67ea0 D_67ea0 (S - 2160) D60. zld F_67ea4 D_67ea4 (S - 2168) D68. zld F_67ea8 D_67ea8 (S - 2176) D76.
  zld F_67eac D_67eac (S - 2184) D84. zld F_67eb0 D_67eb0 (S - 2192) D92. zld F_67eb4 D_67eb4 (S - 2200) D00. zld F_67eb8 D_67eb8 (S - 2208) D08.
  zld F_67ebc D_67ebc (S - 2216) D16. zld F_67ec0 D_67ec0 (S - 2224) D24.
  zstep F_67ec4 D_67ec4.
  stepjr F_67ec8 D_67ec8 (0x60494 : bv 64)%bv ltac:(gres; bveq).
  zstep F_60494 D_60494. zstep F_60498 D_60498. zstep F_6049c D_6049c. zstep F_604a0 D_604a0.
  stepn F_604a4 D_604a4.
  zstep F_3df04 D_3df04.
  zsd F_3df08 D_3df08 (S - 2152) (U (0x604a8 : bv 64)%bv) ltac:(rewok W).
  zsd F_3df0c D_3df0c (S - 2160) S ltac:(rewok W).
  zsd F_3df10 D_3df10 (S - 2168) n ltac:(rewok W).
  zsd F_3df14 D_3df14 (S - 2176) 16 ltac:(rewok W).
  zstep F_3df18 D_3df18. zstep F_3df1c D_3df1c. zstep F_3df20 D_3df20.
  zstep F_3df24 D_3df24.
  zbft F_3df28 D_3df28.
  stepn F_3df2c D_3df2c. rwH. rewrite art_zb_and by lia. rewrite (art_land15_mod16 n) by lia.
  zbft F_3df30 D_3df30.
  zstep F_3df34 D_3df34. zstep F_3df38 D_3df38. zstep F_3df3c D_3df3c. zstep F_3df40 D_3df40. zstep F_3df44 D_3df44. zstep F_3df48 D_3df48.
  stepn F_3df4c D_3df4c.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_ic3_16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S n ub g16 g24 g32 g40 g48 g56 g64 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 -> 0 <= n < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 -> 0 <= g64 < 2 ^ 64 ->
  cellA M (S - 2152) 8 (U (0x604a8 : bv 64)%bv) -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 -> cellA M (S - 64) 8 g64 ->
  msteps ASEGS (mkst regs (0x3df50 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 g64)) raw0 M rom).
Proof.
  intros regs M rom raw0 S n ub g16 g24 g32 g40 g48 g56 g64 H2 H10 Hub HS HS' Hret Hn Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Hg64 C52 C60 C68 C76 C8 C16 C24 C32 C40 C48 C56 C64.
  zbft F_3df50 D_3df50.
  zld F_3df54 D_3df54 (S - 2152) C52. zld F_3df58 D_3df58 (S - 2160) C60. zld F_3df5c D_3df5c (S - 2168) C68. zld F_3df60 D_3df60 (S - 2176) C76.
  zstep F_3df64 D_3df64.
  stepjr F_3df68 D_3df68 (0x604a8 : bv 64)%bv ltac:(gres; bveq).
  zstep F_604a8 D_604a8.
  zld F_604ac D_604ac (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_604b0 D_604b0 (S - 16) C16. zld F_604b4 D_604b4 (S - 24) C24. zld F_604b8 D_604b8 (S - 32) C32.
  zld F_604bc D_604bc (S - 40) C40. zld F_604c0 D_604c0 (S - 48) C48. zld F_604c4 D_604c4 (S - 56) C56. zld F_604c8 D_604c8 (S - 64) C64.
  zstep F_604cc D_604cc.
  stepret F_604d0 D_604d0 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
