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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtPoison EbtAllocG EbtUnwind EbtDepotA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r5fac4_60344 Eb0_code_r67bcc_67d3c Eb0_code_r3cf10_3de98.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_land15_mod16 : forall n, 0 <= n -> n mod 16 = 0 -> Z.land n 15 = 0.
Proof. intros n Hn H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_icu1_16 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 16 -> getr regs 11 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x69c000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x69c000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x69c000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x69c000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x146dd8 1 1 -> cellA M 0x146dfc 4 30 -> cellA M 0x13d8b8 8 0x1d7c28 -> cellA M (0x1d7c28 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x7b10c : word) M rom) (mkst regs1 (0x9bafc : word) M1 rom)
    /\ getr regs1 1 = (0x83144 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2224) /\ getr regs1 10 = Z_to_bv 64 (S - 2136)
    /\ getr regs1 11 = Z_to_bv 64 0x7b1a4 /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2288 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21)) /\ cellA M1 (S - 64) 8 (U (getr regs 22))
    /\ cellA M1 (S - 2152) 8 0x7b200 /\ cellA M1 (S - 2160) 8 S /\ cellA M1 (S - 2168) 8 n /\ cellA M1 (S - 2176) 8 16 /\ cellA M1 (S - 2184) 8 (U (0x7b1a4 : bv 64)%bv)
    /\ cellA M1 (S - 2192) 8 1 /\ cellA M1 (S - 2200) 8 (S - 2136) /\ cellA M1 (S - 2208) 8 (S - 89)
    /\ cellA M1 (S - 2216) 8 (U (getr regs 23)) /\ cellA M1 (S - 2224) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2136) 8 (S - 2120) /\ cellA M1 (S - 2128) 4 0 /\ cellA M1 (S - 2124) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_7b0bc D_7b0bc.
    zsd F_7b0c0 D_7b0c0 (S - 8) (U raw0) ltac:(rewok W). zsd F_7b0c4 D_7b0c4 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_7b0c8 D_7b0c8 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7b0cc D_7b0cc (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_7b0d0 D_7b0d0 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_7b0d4 D_7b0d4 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_7b0d8 D_7b0d8 (S - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_7b0dc D_7b0dc (S - 64) (U (getr regs 22)) ltac:(rewok W).
    zstep F_7b0e0 D_7b0e0. zstep F_7b0e4 D_7b0e4. zstep F_7b0e8 D_7b0e8. zstep F_7b0ec D_7b0ec. zstep F_7b0f0 D_7b0f0.
    zstep F_7b0f4 D_7b0f4. zstep F_7b0f8 D_7b0f8. zstep F_7b0fc D_7b0fc. zstep F_7b100 D_7b100. zstep F_7b104 D_7b104.
    zsd F_7b108 D_7b108 (S - 80) 0 ltac:(rewok W).
    zsd F_7b10c D_7b10c (S - 2136) (S - 2120) ltac:(rewok W).
    zsd F_7b110 D_7b110 (S - 2128) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2128)) by lia. replace (S - 2128 + 4) with (S - 2124) by lia.
    stepn F_7b114 D_7b114.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7b118 D_7b118.
    zbtk F_7b11c D_7b11c.
    stepn F_7b150 D_7b150.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_7b154 D_7b154.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x13d8b8 8 0x1d7c28) by zcell; assert (Cfast' : cellA X (0x1d7c28 + 34) 1 1) by zcell end.
    zld F_7b158 D_7b158 0x13d8b8 Cg38'. zlbu F_7b15c D_7b15c (0x1d7c28 + 34) Cfast'.
    zstep F_7b160 D_7b160.
    stepn F_7b164 D_7b164.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7b168 D_7b168. zstep F_7b16c D_7b16c. zstep F_7b170 D_7b170.
    stepn F_7b174 D_7b174. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_7b178 D_7b178.
    zsd F_7b17c D_7b17c (S - 80) S ltac:(rewok W).
    zbtk F_7b180 D_7b180.
    zstep F_7b194 D_7b194. zstep F_7b198 D_7b198. zstep F_7b19c D_7b19c. zstep F_7b1a0 D_7b1a0. zstep F_7b1a4 D_7b1a4. zstep F_7b1a8 D_7b1a8.
    stepn F_7b1ac D_7b1ac.

    zstep F_82fd8 D_82fd8.
    zsd F_82fdc D_82fdc (S - 2152) 0x7b200 ltac:(rewok W). zsd F_82fe0 D_82fe0 (S - 2160) S ltac:(rewok W). zsd F_82fe4 D_82fe4 (S - 2168) n ltac:(rewok W).
    zsd F_82fe8 D_82fe8 (S - 2176) 16 ltac:(rewok W). zsd F_82fec D_82fec (S - 2184) (U (0x7b1a4 : bv 64)%bv) ltac:(rewok W). zsd F_82ff0 D_82ff0 (S - 2192) 1 ltac:(rewok W).
    zsd F_82ff4 D_82ff4 (S - 2200) (S - 2136) ltac:(rewok W). zsd F_82ff8 D_82ff8 (S - 2208) (S - 89) ltac:(rewok W).
    zsd F_82ffc D_82ffc (S - 2216) (U (getr regs 23)) ltac:(rewok W). zsd F_83000 D_83000 (S - 2224) (U (getr regs 24)) ltac:(rewok W).
    zstep F_83004 D_83004. zstep F_83008 D_83008. zstep F_8300c D_8300c. zstep F_83010 D_83010. zstep F_83014 D_83014. zstep F_83018 D_83018.
    zsw F_8301c D_8301c (S - 2128) 0 ltac:(rewok W).
    stepn F_83020 D_83020.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_83024 D_83024.
    stepn F_83028 D_83028.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2224) tp key tsd ctx t).
    { unfold art_tsd. repeat split; try lia; zcell. }
    zbft F_8302c D_8302c.
    zstep F_83030 D_83030.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
    zlbu F_83034 D_83034 (t + 2047 + 1121) Cunw'.
    zstep F_83038 D_83038.
    zsb F_8303c D_8303c (t + 2047 + 1121) 1 ltac:(rewok Wt).
    zbft F_83040 D_83040.
    zstep F_83044 D_83044.
    stepn F_83048 D_83048.
    zcall (art_stack_top_fn _ _ _ _ t top bot).
    zstep F_8304c D_8304c. zstep F_83050 D_83050.
    stepn F_83054 D_83054.
    zcall (art_stack_bottom_fn _ _ _ _ t top bot).
    zstep F_83058 D_83058.
    zbft F_8305c D_8305c.
    zstep F_83060 D_83060. zstep F_83064 D_83064. zstep F_83068 D_83068. zstep F_8306c D_8306c. zstep F_83070 D_83070. zstep F_83074 D_83074. zstep F_83078 D_83078.
    stepn F_8307c D_8307c.
    stepn F_830f0 D_830f0.
    zcall (art_unwind_fn _ _ _ _ (S - 2224) (S - 2136) 0x7b1a4 S top bot).
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
  cellA M (S - 2152) 8 0x7b200 -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 -> cellA M (S - 2184) 8 (U (0x7b1a4 : bv 64)%bv) ->
  cellA M (S - 2192) 8 1 -> cellA M (S - 2200) 8 (S - 2136) -> cellA M (S - 2208) 8 (S - 89) -> cellA M (S - 2216) 8 f23 -> cellA M (S - 2224) 8 f24 ->
  msteps ASEGS (mkst regs (0x83144 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x541d4 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (S - 2136))) 9 (Z_to_bv 64 16)) 10 (Z_to_bv 64 0x142a98)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 16)) 13 (Z_to_bv 64 (S - 2136))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 16)) 19 (Z_to_bv 64 (U (0x7b1a4 : bv 64)%bv))) 20 (Z_to_bv 64 1)) 21 (Z_to_bv 64 (S - 2136))) 22 (Z_to_bv 64 (S - 89))) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x535f4 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2152) (U (0x7b214 : bv 64)%bv)) (S - 2160) S) (S - 2168) n) (S - 2176) 16) rom).
Proof.
  intros regs M rom S n t f23 f24 H2 H24 HS HS' Hn Hn16 Ht Ht' Atsp Hf23 Hf24 W Wt C52 C60 C68 C76 C84 C92 C00 C08 C16 C24.
  zsb F_830f4 D_830f4 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D52 : cellA X (S - 2152) 8 0x7b200) by zcell; assert (D60 : cellA X (S - 2160) 8 S) by zcell; assert (D68 : cellA X (S - 2168) 8 n) by zcell;
    assert (D76 : cellA X (S - 2176) 8 16) by zcell; assert (D84 : cellA X (S - 2184) 8 (U (0x7b1a4 : bv 64)%bv)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 1) by zcell; assert (D00 : cellA X (S - 2200) 8 (S - 2136)) by zcell;
    assert (D08 : cellA X (S - 2208) 8 (S - 89)) by zcell; assert (D16 : cellA X (S - 2216) 8 f23) by zcell; assert (D24 : cellA X (S - 2224) 8 f24) by zcell end.
  zld F_830f8 D_830f8 (S - 2152) D52. zld F_830fc D_830fc (S - 2160) D60. zld F_83100 D_83100 (S - 2168) D68. zld F_83104 D_83104 (S - 2176) D76.
  zld F_83108 D_83108 (S - 2184) D84. zld F_8310c D_8310c (S - 2192) D92. zld F_83110 D_83110 (S - 2200) D00. zld F_83114 D_83114 (S - 2208) D08.
  zld F_83118 D_83118 (S - 2216) D16. zld F_8311c D_8311c (S - 2224) D24.
  zstep F_83120 D_83120.
  stepjr F_83124 D_83124 (0x7b200 : bv 64)%bv ltac:(gres; bveq).
  zstep F_7b1b0 D_7b1b0. zstep F_7b1b4 D_7b1b4. zstep F_7b1b8 D_7b1b8. zstep F_7b1bc D_7b1bc.
  stepn F_7b1c0 D_7b1c0.
  zstep F_54138 D_54138.
  zsd F_5413c D_5413c (S - 2152) (U (0x7b214 : bv 64)%bv) ltac:(rewok W).
  zsd F_54140 D_54140 (S - 2160) S ltac:(rewok W).
  zsd F_54144 D_54144 (S - 2168) n ltac:(rewok W).
  zsd F_54148 D_54148 (S - 2176) 16 ltac:(rewok W).
  zstep F_5414c D_5414c. zstep F_54150 D_54150. zstep F_54154 D_54154.
  zstep F_54158 D_54158.
  zbft F_5415c D_5415c.
  stepn F_54160 D_54160. rwH. rewrite art_zb_and by lia. rewrite (art_land15_mod16 n) by lia.
  zbft F_54164 D_54164.
  zstep F_54168 D_54168. zstep F_5416c D_5416c. zstep F_54170 D_54170. zstep F_54174 D_54174. zstep F_54178 D_54178. zstep F_5417c D_5417c.
  stepn F_54180 D_54180.
  zret.
Qed.

#[using="Type"] Lemma art_ic3_16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S n ub g16 g24 g32 g40 g48 g56 g64 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 -> 0 <= n < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 -> 0 <= g64 < 2 ^ 64 ->
  cellA M (S - 2152) 8 (U (0x7b214 : bv 64)%bv) -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 -> cellA M (S - 64) 8 g64 ->
  msteps ASEGS (mkst regs (0x541d4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 g64)) raw0 M rom).
Proof.
  intros regs M rom raw0 S n ub g16 g24 g32 g40 g48 g56 g64 H2 H10 Hub HS HS' Hret Hn Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Hg64 C52 C60 C68 C76 C8 C16 C24 C32 C40 C48 C56 C64.
  zbft F_54184 D_54184.
  zld F_54188 D_54188 (S - 2152) C52. zld F_5418c D_5418c (S - 2160) C60. zld F_54190 D_54190 (S - 2168) C68. zld F_54194 D_54194 (S - 2176) C76.
  zstep F_54198 D_54198.
  stepjr F_5419c D_5419c (0x7b214 : bv 64)%bv ltac:(gres; bveq).
  zstep F_7b1c4 D_7b1c4.
  zld F_7b1c8 D_7b1c8 (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_7b1cc D_7b1cc (S - 16) C16. zld F_7b1d0 D_7b1d0 (S - 24) C24. zld F_7b1d4 D_7b1d4 (S - 32) C32.
  zld F_7b1d8 D_7b1d8 (S - 40) C40. zld F_7b1dc D_7b1dc (S - 48) C48. zld F_7b1e0 D_7b1e0 (S - 56) C56. zld F_7b1e4 D_7b1e4 (S - 64) C64.
  zstep F_7b1e8 D_7b1e8.
  stepret F_7b1ec D_7b1ec raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
