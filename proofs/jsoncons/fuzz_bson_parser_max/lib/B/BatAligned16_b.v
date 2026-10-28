(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b BatDepotA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b Ba0_code_r67bcc_67d3c_b Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_land15_mod16 : forall n, 0 <= n -> n mod 16 = 0 -> Z.land n 15 = 0.
Proof. intros n Hn H. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. exact H. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_icu1_16 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 16 -> getr regs 11 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x140918 1 1 -> cellA M 0x14093c 4 30 -> cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x79f60 : word) M rom) (mkst regs1 (0x9a950 : word) M1 rom)
    /\ getr regs1 1 = (0x81f98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2224) /\ getr regs1 10 = Z_to_bv 64 (S - 2136)
    /\ getr regs1 11 = Z_to_bv 64 0x79ff8 /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2288 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21)) /\ cellA M1 (S - 64) 8 (U (getr regs 22))
    /\ cellA M1 (S - 2152) 8 0x7a054 /\ cellA M1 (S - 2160) 8 S /\ cellA M1 (S - 2168) 8 n /\ cellA M1 (S - 2176) 8 16 /\ cellA M1 (S - 2184) 8 (U (0x79ff8 : bv 64)%bv)
    /\ cellA M1 (S - 2192) 8 1 /\ cellA M1 (S - 2200) 8 (S - 2136) /\ cellA M1 (S - 2208) 8 (S - 89)
    /\ cellA M1 (S - 2216) 8 (U (getr regs 23)) /\ cellA M1 (S - 2224) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2136) 8 (S - 2120) /\ cellA M1 (S - 2128) 4 0 /\ cellA M1 (S - 2124) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_79b48 D_79b48.
    zsd F_79b4c D_79b4c (S - 8) (U raw0) ltac:(rewok W). zsd F_79b50 D_79b50 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_79b54 D_79b54 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_79b58 D_79b58 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_79b5c D_79b5c (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_79b60 D_79b60 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_79b64 D_79b64 (S - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_79b68 D_79b68 (S - 64) (U (getr regs 22)) ltac:(rewok W).
    zstep F_79b6c D_79b6c. zstep F_79b70 D_79b70. zstep F_79b74 D_79b74. zstep F_79b78 D_79b78. zstep F_79b7c D_79b7c.
    zstep F_79b80 D_79b80. zstep F_79b84 D_79b84. zstep F_79b88 D_79b88. zstep F_79b8c D_79b8c. zstep F_79b90 D_79b90.
    zsd F_79b94 D_79b94 (S - 80) 0 ltac:(rewok W).
    zsd F_79b98 D_79b98 (S - 2136) (S - 2120) ltac:(rewok W).
    zsd F_79b9c D_79b9c (S - 2128) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2128)) by lia. replace (S - 2128 + 4) with (S - 2124) by lia.
    stepn F_79ba0 D_79ba0.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_79ba4 D_79ba4.
    zbtk F_79ba8 D_79ba8.
    stepn F_79bdc D_79bdc.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_79be0 D_79be0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x1374b0 8 0x1d1768) by zcell; assert (Cfast' : cellA X (0x1d1768 + 34) 1 1) by zcell end.
    zld F_79be4 D_79be4 0x1374b0 Cg38'. zlbu F_79be8 D_79be8 (0x1d1768 + 34) Cfast'.
    zstep F_79bec D_79bec.
    stepn F_79bf0 D_79bf0.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_79bf4 D_79bf4. zstep F_79bf8 D_79bf8. zstep F_79bfc D_79bfc.
    stepn F_79c00 D_79c00. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_79c04 D_79c04.
    zsd F_79c08 D_79c08 (S - 80) S ltac:(rewok W).
    zbtk F_79c0c D_79c0c.
    zstep F_79c20 D_79c20. zstep F_79c24 D_79c24. zstep F_79c28 D_79c28. zstep F_79c2c D_79c2c. zstep F_79c30 D_79c30. zstep F_79c34 D_79c34.
    stepn F_79c38 D_79c38.
    (* [comment removed for export] *)
    zstep F_81a64 D_81a64.
    zsd F_81a68 D_81a68 (S - 2152) 0x7a054 ltac:(rewok W). zsd F_81a6c D_81a6c (S - 2160) S ltac:(rewok W). zsd F_81a70 D_81a70 (S - 2168) n ltac:(rewok W).
    zsd F_81a74 D_81a74 (S - 2176) 16 ltac:(rewok W). zsd F_81a78 D_81a78 (S - 2184) (U (0x79ff8 : bv 64)%bv) ltac:(rewok W). zsd F_81a7c D_81a7c (S - 2192) 1 ltac:(rewok W).
    zsd F_81a80 D_81a80 (S - 2200) (S - 2136) ltac:(rewok W). zsd F_81a84 D_81a84 (S - 2208) (S - 89) ltac:(rewok W).
    zsd F_81a88 D_81a88 (S - 2216) (U (getr regs 23)) ltac:(rewok W). zsd F_81a8c D_81a8c (S - 2224) (U (getr regs 24)) ltac:(rewok W).
    zstep F_81a90 D_81a90. zstep F_81a94 D_81a94. zstep F_81a98 D_81a98. zstep F_81a9c D_81a9c. zstep F_81aa0 D_81aa0. zstep F_81aa4 D_81aa4.
    zsw F_81aa8 D_81aa8 (S - 2128) 0 ltac:(rewok W).
    stepn F_81aac D_81aac.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_81ab0 D_81ab0.
    stepn F_81ab4 D_81ab4.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2224) tp key tsd ctx t).
    { unfold art_tsd. repeat split; try lia; zcell. }
    zbft F_81ab8 D_81ab8.
    zstep F_81abc D_81abc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
    zlbu F_81ac0 D_81ac0 (t + 2047 + 1121) Cunw'.
    zstep F_81ac4 D_81ac4.
    zsb F_81ac8 D_81ac8 (t + 2047 + 1121) 1 ltac:(rewok Wt).
    zbft F_81acc D_81acc.
    zstep F_81ad0 D_81ad0.
    stepn F_81ad4 D_81ad4.
    zcall (art_stack_top_fn _ _ _ _ t top bot).
    zstep F_81ad8 D_81ad8. zstep F_81adc D_81adc.
    stepn F_81ae0 D_81ae0.
    zcall (art_stack_bottom_fn _ _ _ _ t top bot).
    zstep F_81ae4 D_81ae4.
    zbft F_81ae8 D_81ae8.
    zstep F_81aec D_81aec. zstep F_81af0 D_81af0. zstep F_81af4 D_81af4. zstep F_81af8 D_81af8. zstep F_81afc D_81afc. zstep F_81b00 D_81b00. zstep F_81b04 D_81b04.
    stepn F_81b08 D_81b08.
    stepn F_81b7c D_81b7c.
    zcall (art_unwind_fn _ _ _ _ (S - 2224) (S - 2136) 0x79ff8 S top bot).
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

(* [comment removed for export] *)
#[using="Type"] Lemma art_icu2_16_fn : forall regs (M rom : word -> option byte) (S n t f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2224) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> n mod 16 = 0 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2152) 8 0x7a054 -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 -> cellA M (S - 2184) 8 (U (0x79ff8 : bv 64)%bv) ->
  cellA M (S - 2192) 8 1 -> cellA M (S - 2200) 8 (S - 2136) -> cellA M (S - 2208) 8 (S - 89) -> cellA M (S - 2216) 8 f23 -> cellA M (S - 2224) 8 f24 ->
  msteps ASEGS (mkst regs (0x81f98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x531c4 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (S - 2136))) 9 (Z_to_bv 64 16)) 10 (Z_to_bv 64 0x13c5d8)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 16)) 13 (Z_to_bv 64 (S - 2136))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 16)) 19 (Z_to_bv 64 (U (0x79ff8 : bv 64)%bv))) 20 (Z_to_bv 64 1)) 21 (Z_to_bv 64 (S - 2136))) 22 (Z_to_bv 64 (S - 89))) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x525e4 : word) (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2152) (U (0x7a068 : bv 64)%bv)) (S - 2160) S) (S - 2168) n) (S - 2176) 16) rom).
Proof.
  intros regs M rom S n t f23 f24 H2 H24 HS HS' Hn Hn16 Ht Ht' Atsp Hf23 Hf24 W Wt C52 C60 C68 C76 C84 C92 C00 C08 C16 C24.
  zsb F_81b80 D_81b80 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D52 : cellA X (S - 2152) 8 0x7a054) by zcell; assert (D60 : cellA X (S - 2160) 8 S) by zcell; assert (D68 : cellA X (S - 2168) 8 n) by zcell;
    assert (D76 : cellA X (S - 2176) 8 16) by zcell; assert (D84 : cellA X (S - 2184) 8 (U (0x79ff8 : bv 64)%bv)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 1) by zcell; assert (D00 : cellA X (S - 2200) 8 (S - 2136)) by zcell;
    assert (D08 : cellA X (S - 2208) 8 (S - 89)) by zcell; assert (D16 : cellA X (S - 2216) 8 f23) by zcell; assert (D24 : cellA X (S - 2224) 8 f24) by zcell end.
  zld F_81b84 D_81b84 (S - 2152) D52. zld F_81b88 D_81b88 (S - 2160) D60. zld F_81b8c D_81b8c (S - 2168) D68. zld F_81b90 D_81b90 (S - 2176) D76.
  zld F_81b94 D_81b94 (S - 2184) D84. zld F_81b98 D_81b98 (S - 2192) D92. zld F_81b9c D_81b9c (S - 2200) D00. zld F_81ba0 D_81ba0 (S - 2208) D08.
  zld F_81ba4 D_81ba4 (S - 2216) D16. zld F_81ba8 D_81ba8 (S - 2224) D24.
  zstep F_81bac D_81bac.
  stepjr F_81bb0 D_81bb0 (0x7a054 : bv 64)%bv ltac:(gres; bveq).
  zstep F_79c3c D_79c3c. zstep F_79c40 D_79c40. zstep F_79c44 D_79c44. zstep F_79c48 D_79c48.
  stepn F_79c4c D_79c4c.
  zstep F_52d60 D_52d60.
  zsd F_52d64 D_52d64 (S - 2152) (U (0x7a068 : bv 64)%bv) ltac:(rewok W).
  zsd F_52d68 D_52d68 (S - 2160) S ltac:(rewok W).
  zsd F_52d6c D_52d6c (S - 2168) n ltac:(rewok W).
  zsd F_52d70 D_52d70 (S - 2176) 16 ltac:(rewok W).
  zstep F_52d74 D_52d74. zstep F_52d78 D_52d78. zstep F_52d7c D_52d7c.
  zstep F_52d80 D_52d80.
  zbft F_52d84 D_52d84.
  stepn F_52d88 D_52d88. rwH. rewrite art_zb_and by lia. rewrite (art_land15_mod16 n) by lia.
  zbft F_52d8c D_52d8c.
  zstep F_52d90 D_52d90. zstep F_52d94 D_52d94. zstep F_52d98 D_52d98. zstep F_52d9c D_52d9c. zstep F_52da0 D_52da0. zstep F_52da4 D_52da4.
  stepn F_52da8 D_52da8.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic3_16_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S n ub g16 g24 g32 g40 g48 g56 g64 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 -> 0 <= n < 2 ^ 64 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 -> 0 <= g64 < 2 ^ 64 ->
  cellA M (S - 2152) 8 (U (0x7a068 : bv 64)%bv) -> cellA M (S - 2160) 8 S -> cellA M (S - 2168) 8 n -> cellA M (S - 2176) 8 16 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 -> cellA M (S - 64) 8 g64 ->
  msteps ASEGS (mkst regs (0x531c4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 g64)) raw0 M rom).
Proof.
  intros regs M rom raw0 S n ub g16 g24 g32 g40 g48 g56 g64 H2 H10 Hub HS HS' Hret Hn Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Hg64 C52 C60 C68 C76 C8 C16 C24 C32 C40 C48 C56 C64.
  zbft F_52dac D_52dac.
  zld F_52db0 D_52db0 (S - 2152) C52. zld F_52db4 D_52db4 (S - 2160) C60. zld F_52db8 D_52db8 (S - 2168) C68. zld F_52dbc D_52dbc (S - 2176) C76.
  zstep F_52dc0 D_52dc0.
  stepjr F_52dc4 D_52dc4 (0x7a068 : bv 64)%bv ltac:(gres; bveq).
  zstep F_79c50 D_79c50.
  zld F_79c54 D_79c54 (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_79c58 D_79c58 (S - 16) C16. zld F_79c5c D_79c5c (S - 24) C24. zld F_79c60 D_79c60 (S - 32) C32.
  zld F_79c64 D_79c64 (S - 40) C40. zld F_79c68 D_79c68 (S - 48) C48. zld F_79c6c D_79c6c (S - 56) C56. zld F_79c70 D_79c70 (S - 64) C64.
  zstep F_79c74 D_79c74.
  stepret F_79c78 D_79c78 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
