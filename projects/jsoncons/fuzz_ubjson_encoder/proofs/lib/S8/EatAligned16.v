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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison EatAllocG EatUnwind EatDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344 Ea0_code_r67bcc_67d3c Ea0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_land15_mod16 : forall n, 0 <= n -> n mod 16 = 0 -> Z.land n 15 = 0.
Proof. intros n Hn H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_icu1_16 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 16 -> getr regs 11 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x698000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x698000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x698000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x698000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x1426d8 1 1 -> cellA M 0x1426fc 4 30 -> cellA M 0x1391a8 8 0x1d3528 -> cellA M (0x1d3528 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x7a8e4 : word) M rom) (mkst regs1 (0x9b2d4 : word) M1 rom)
    /\ getr regs1 1 = (0x8291c : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2224) /\ getr regs1 10 = Z_to_bv 64 (S - 2136)
    /\ getr regs1 11 = Z_to_bv 64 0x7a97c /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2288 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21)) /\ cellA M1 (S - 64) 8 (U (getr regs 22))
    /\ cellA M1 (S - 2152) 8 0x7a9d8 /\ cellA M1 (S - 2160) 8 S /\ cellA M1 (S - 2168) 8 n /\ cellA M1 (S - 2176) 8 16 /\ cellA M1 (S - 2184) 8 (U (0x7a97c : bv 64)%bv)
    /\ cellA M1 (S - 2192) 8 1 /\ cellA M1 (S - 2200) 8 (S - 2136) /\ cellA M1 (S - 2208) 8 (S - 89)
    /\ cellA M1 (S - 2216) 8 (U (getr regs 23)) /\ cellA M1 (S - 2224) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2136) 8 (S - 2120) /\ cellA M1 (S - 2128) 4 0 /\ cellA M1 (S - 2124) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_7a894 D_7a894.
    zsd F_7a898 D_7a898 (S - 8) (U raw0) ltac:(rewok W). zsd F_7a89c D_7a89c (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_7a8a0 D_7a8a0 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7a8a4 D_7a8a4 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_7a8a8 D_7a8a8 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_7a8ac D_7a8ac (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_7a8b0 D_7a8b0 (S - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_7a8b4 D_7a8b4 (S - 64) (U (getr regs 22)) ltac:(rewok W).
    zstep F_7a8b8 D_7a8b8. zstep F_7a8bc D_7a8bc. zstep F_7a8c0 D_7a8c0. zstep F_7a8c4 D_7a8c4. zstep F_7a8c8 D_7a8c8.
    zstep F_7a8cc D_7a8cc. zstep F_7a8d0 D_7a8d0. zstep F_7a8d4 D_7a8d4. zstep F_7a8d8 D_7a8d8. zstep F_7a8dc D_7a8dc.
    zsd F_7a8e0 D_7a8e0 (S - 80) 0 ltac:(rewok W).
    zsd F_7a8e4 D_7a8e4 (S - 2136) (S - 2120) ltac:(rewok W).
    zsd F_7a8e8 D_7a8e8 (S - 2128) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2128)) by lia. replace (S - 2128 + 4) with (S - 2124) by lia.
    stepn F_7a8ec D_7a8ec.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7a8f0 D_7a8f0.
    zbtk F_7a8f4 D_7a8f4.
    stepn F_7a928 D_7a928.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_7a92c D_7a92c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x1391a8 8 0x1d3528) by zcell; assert (Cfast' : cellA X (0x1d3528 + 34) 1 1) by zcell end.
    zld F_7a930 D_7a930 0x1391a8 Cg38'. zlbu F_7a934 D_7a934 (0x1d3528 + 34) Cfast'.
    zstep F_7a938 D_7a938.
    stepn F_7a93c D_7a93c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7a940 D_7a940. zstep F_7a944 D_7a944. zstep F_7a948 D_7a948.
    stepn F_7a94c D_7a94c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_7a950 D_7a950.
    zsd F_7a954 D_7a954 (S - 80) S ltac:(rewok W).
    zbtk F_7a958 D_7a958.
    zstep F_7a96c D_7a96c. zstep F_7a970 D_7a970. zstep F_7a974 D_7a974. zstep F_7a978 D_7a978. zstep F_7a97c D_7a97c. zstep F_7a980 D_7a980.
    stepn F_7a984 D_7a984.

    zstep F_827b0 D_827b0.
    zsd F_827b4 D_827b4 (S - 2152) 0x7a9d8 ltac:(rewok W). zsd F_827b8 D_827b8 (S - 2160) S ltac:(rewok W). zsd F_827bc D_827bc (S - 2168) n ltac:(rewok W).
    zsd F_827c0 D_827c0 (S - 2176) 16 ltac:(rewok W). zsd F_827c4 D_827c4 (S - 2184) (U (0x7a97c : bv 64)%bv) ltac:(rewok W). zsd F_827c8 D_827c8 (S - 2192) 1 ltac:(rewok W).
    zsd F_827cc D_827cc (S - 2200) (S - 2136) ltac:(rewok W). zsd F_827d0 D_827d0 (S - 2208) (S - 89) ltac:(rewok W).
    zsd F_827d4 D_827d4 (S - 2216) (U (getr regs 23)) ltac:(rewok W). zsd F_827d8 D_827d8 (S - 2224) (U (getr regs 24)) ltac:(rewok W).
    zstep F_827dc D_827dc. zstep F_827e0 D_827e0. zstep F_827e4 D_827e4. zstep F_827e8 D_827e8. zstep F_827ec D_827ec. zstep F_827f0 D_827f0.
    zsw F_827f4 D_827f4 (S - 2128) 0 ltac:(rewok W).
    stepn F_827f8 D_827f8.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_827fc D_827fc.
    stepn F_82800 D_82800.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2224) tp key tsd ctx t).
    { unfold art_tsd. repeat split; try lia; zcell. }
    zbft F_82804 D_82804.
    zstep F_82808 D_82808.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
    zlbu F_8280c D_8280c (t + 2047 + 1121) Cunw'.
    zstep F_82810 D_82810.
    zsb F_82814 D_82814 (t + 2047 + 1121) 1 ltac:(rewok Wt).
    zbft F_82818 D_82818.
    zstep F_8281c D_8281c.
    stepn F_82820 D_82820.
    zcall (art_stack_top_fn _ _ _ _ t top bot).
    zstep F_82824 D_82824. zstep F_82828 D_82828.
    stepn F_8282c D_8282c.
    zcall (art_stack_bottom_fn _ _ _ _ t top bot).
    zstep F_82830 D_82830.
    zbft F_82834 D_82834.
    zstep F_82838 D_82838. zstep F_8283c D_8283c. zstep F_82840 D_82840. zstep F_82844 D_82844. zstep F_82848 D_82848. zstep F_8284c D_8284c. zstep F_82850 D_82850.
    stepn F_82854 D_82854.
    stepn F_828c8 D_828c8.
    zcall (art_unwind_fn _ _ _ _ (S - 2224) (S - 2136) 0x7a97c S top bot).
    apply mst_refl.
  - zsplit.
    all: lazymatch goal with
         | |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
         | |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
         | |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
         | |- forall x : word, _ => intros x N1 N2; zagree
         | |- wr _ _ _ _ => zwr
         | |- cell _ _ _ _ _ => zcell
         end.
Qed.

#[using="Type"] Lemma art_icu2_16_fn : forall regs (M rom : word -> option byte) (S n t f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2224) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> n mod 16 = 0 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2152) 8 0x7a9d8 -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 -> cellA M (S - 2184) 8 (U (0x7a97c : bv 64)%bv) ->
  cellA M (S - 2192) 8 1 -> cellA M (S - 2200) 8 (S - 2136) -> cellA M (S - 2208) 8 (S - 89) -> cellA M (S - 2216) 8 f23 -> cellA M (S - 2224) 8 f24 ->
  msteps ASEGS (mkst regs (0x8291c : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x539ac : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (S - 2136))) 9 (Z_to_bv 64 16)) 10 (Z_to_bv 64 0x13e398)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 16)) 13 (Z_to_bv 64 (S - 2136))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 16)) 19 (Z_to_bv 64 (U (0x7a97c : bv 64)%bv))) 20 (Z_to_bv 64 1)) 21 (Z_to_bv 64 (S - 2136))) 22 (Z_to_bv 64 (S - 89))) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x52dcc : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2152) (U (0x7a9ec : bv 64)%bv)) (S - 2160) S) (S - 2168) n) (S - 2176) 16) rom).
Proof.
  intros regs M rom S n t f23 f24 H2 H24 HS HS' Hn Hn16 Ht Ht' Atsp Hf23 Hf24 W Wt C52 C60 C68 C76 C84 C92 C00 C08 C16 C24.
  zsb F_828cc D_828cc (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D52 : cellA X (S - 2152) 8 0x7a9d8) by zcell; assert (D60 : cellA X (S - 2160) 8 S) by zcell; assert (D68 : cellA X (S - 2168) 8 n) by zcell;
    assert (D76 : cellA X (S - 2176) 8 16) by zcell; assert (D84 : cellA X (S - 2184) 8 (U (0x7a97c : bv 64)%bv)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 1) by zcell; assert (D00 : cellA X (S - 2200) 8 (S - 2136)) by zcell;
    assert (D08 : cellA X (S - 2208) 8 (S - 89)) by zcell; assert (D16 : cellA X (S - 2216) 8 f23) by zcell; assert (D24 : cellA X (S - 2224) 8 f24) by zcell end.
  zld F_828d0 D_828d0 (S - 2152) D52. zld F_828d4 D_828d4 (S - 2160) D60. zld F_828d8 D_828d8 (S - 2168) D68. zld F_828dc D_828dc (S - 2176) D76.
  zld F_828e0 D_828e0 (S - 2184) D84. zld F_828e4 D_828e4 (S - 2192) D92. zld F_828e8 D_828e8 (S - 2200) D00. zld F_828ec D_828ec (S - 2208) D08.
  zld F_828f0 D_828f0 (S - 2216) D16. zld F_828f4 D_828f4 (S - 2224) D24.
  zstep F_828f8 D_828f8.
  stepjr F_828fc D_828fc (0x7a9d8 : bv 64)%bv ltac:(gres; bveq).
  zstep F_7a988 D_7a988. zstep F_7a98c D_7a98c. zstep F_7a990 D_7a990. zstep F_7a994 D_7a994.
  stepn F_7a998 D_7a998.
  zstep F_53910 D_53910.
  zsd F_53914 D_53914 (S - 2152) (U (0x7a9ec : bv 64)%bv) ltac:(rewok W).
  zsd F_53918 D_53918 (S - 2160) S ltac:(rewok W).
  zsd F_5391c D_5391c (S - 2168) n ltac:(rewok W).
  zsd F_53920 D_53920 (S - 2176) 16 ltac:(rewok W).
  zstep F_53924 D_53924. zstep F_53928 D_53928. zstep F_5392c D_5392c.
  zstep F_53930 D_53930.
  zbft F_53934 D_53934.
  stepn F_53938 D_53938. rwH. rewrite art_zb_and by lia. rewrite (art_land15_mod16 n) by lia.
  zbft F_5393c D_5393c.
  zstep F_53940 D_53940. zstep F_53944 D_53944. zstep F_53948 D_53948. zstep F_5394c D_5394c. zstep F_53950 D_53950. zstep F_53954 D_53954.
  stepn F_53958 D_53958.
  zret.
Qed.

#[using="Type"] Lemma art_ic3_16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S n ub g16 g24 g32 g40 g48 g56 g64 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 -> 0 <= n < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 -> 0 <= g64 < 2 ^ 64 ->
  cellA M (S - 2152) 8 (U (0x7a9ec : bv 64)%bv) -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 -> cellA M (S - 64) 8 g64 ->
  msteps ASEGS (mkst regs (0x539ac : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 g64)) raw0 M rom).
Proof.
  intros regs M rom raw0 S n ub g16 g24 g32 g40 g48 g56 g64 H2 H10 Hub HS HS' Hret Hn Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Hg64 C52 C60 C68 C76 C8 C16 C24 C32 C40 C48 C56 C64.
  zbft F_5395c D_5395c.
  zld F_53960 D_53960 (S - 2152) C52. zld F_53964 D_53964 (S - 2160) C60. zld F_53968 D_53968 (S - 2168) C68. zld F_5396c D_5396c (S - 2176) C76.
  zstep F_53970 D_53970.
  stepjr F_53974 D_53974 (0x7a9ec : bv 64)%bv ltac:(gres; bveq).
  zstep F_7a99c D_7a99c.
  zld F_7a9a0 D_7a9a0 (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_7a9a4 D_7a9a4 (S - 16) C16. zld F_7a9a8 D_7a9a8 (S - 24) C24. zld F_7a9ac D_7a9ac (S - 32) C32.
  zld F_7a9b0 D_7a9b0 (S - 40) C40. zld F_7a9b4 D_7a9b4 (S - 48) C48. zld F_7a9b8 D_7a9b8 (S - 56) C56. zld F_7a9bc D_7a9bc (S - 64) C64.
  zstep F_7a9c0 D_7a9c0.
  stepret F_7a9c4 D_7a9c4 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
