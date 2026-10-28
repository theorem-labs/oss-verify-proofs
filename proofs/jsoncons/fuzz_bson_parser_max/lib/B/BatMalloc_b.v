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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b.
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

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_icu1 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x140918 1 1 -> cellA M 0x14093c 4 30 -> cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x799f4 : word) M rom) (mkst regs1 (0x9a950 : word) M1 rom)
    /\ getr regs1 1 = (0x81f98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x79abc /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21))
    /\ cellA M1 (S - 2136) 8 0x79b18 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 n /\ cellA M1 (S - 2160) 8 (U (0x79abc : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
    /\ cellA M1 (S - 2176) 8 (S - 2128) /\ cellA M1 (S - 2184) 8 (S - 81)
    /\ cellA M1 (S - 2192) 8 (U (getr regs 22)) /\ cellA M1 (S - 2200) 8 (U (getr regs 23)) /\ cellA M1 (S - 2208) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2128) 8 (S - 2112) /\ cellA M1 (S - 2120) 4 0 /\ cellA M1 (S - 2116) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_795dc D_795dc.
    zsd F_795e0 D_795e0 (S - 8) (U raw0) ltac:(rewok W). zsd F_795e4 D_795e4 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_795e8 D_795e8 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_795ec D_795ec (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_795f0 D_795f0 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_795f4 D_795f4 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_795f8 D_795f8 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_795fc D_795fc. zstep F_79600 D_79600. zstep F_79604 D_79604. zstep F_79608 D_79608.
    stepn F_7960c D_7960c.
    zcall (art_try_init_fn _ _ _ _ (S - 2128)).
    zbft F_79610 D_79610.
    zstep F_79614 D_79614. zstep F_79618 D_79618. zstep F_7961c D_7961c. zstep F_79620 D_79620. zstep F_79624 D_79624.
    zsd F_79628 D_79628 (S - 72) 0 ltac:(rewok W).
    zsd F_7962c D_7962c (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_79630 D_79630 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_79634 D_79634.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_79638 D_79638.
    zbtk F_7963c D_7963c.
    stepn F_796a0 D_796a0.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_796a4 D_796a4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x1374b0 8 0x1d1768) by zcell; assert (Cfast' : cellA X (0x1d1768 + 34) 1 1) by zcell end.
    zld F_796a8 D_796a8 0x1374b0 Cg38'. zlbu F_796ac D_796ac (0x1d1768 + 34) Cfast'.
    zstep F_796b0 D_796b0.
    stepn F_796b4 D_796b4.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_796b8 D_796b8. zstep F_796bc D_796bc. zstep F_796c0 D_796c0.
    stepn F_796c4 D_796c4. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_796c8 D_796c8.
    zsd F_796cc D_796cc (S - 72) S ltac:(rewok W).
    zbtk F_796d0 D_796d0.
    zstep F_796e4 D_796e4. zstep F_796e8 D_796e8. zstep F_796ec D_796ec. zstep F_796f0 D_796f0. zstep F_796f4 D_796f4. zstep F_796f8 D_796f8.
    stepn F_796fc D_796fc.
    (* [comment removed for export] *)
    zstep F_81a64 D_81a64.
    zsd F_81a68 D_81a68 (S - 2136) 0x79b18 ltac:(rewok W). zsd F_81a6c D_81a6c (S - 2144) S ltac:(rewok W). zsd F_81a70 D_81a70 (S - 2152) n ltac:(rewok W).
    zsd F_81a74 D_81a74 (S - 2160) (U (0x79abc : bv 64)%bv) ltac:(rewok W). zsd F_81a78 D_81a78 (S - 2168) 1 ltac:(rewok W). zsd F_81a7c D_81a7c (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_81a80 D_81a80 (S - 2184) (S - 81) ltac:(rewok W). zsd F_81a84 D_81a84 (S - 2192) (U (getr regs 22)) ltac:(rewok W).
    zsd F_81a88 D_81a88 (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd F_81a8c D_81a8c (S - 2208) (U (getr regs 24)) ltac:(rewok W).
    zstep F_81a90 D_81a90. zstep F_81a94 D_81a94. zstep F_81a98 D_81a98. zstep F_81a9c D_81a9c. zstep F_81aa0 D_81aa0. zstep F_81aa4 D_81aa4.
    zsw F_81aa8 D_81aa8 (S - 2120) 0 ltac:(rewok W).
    stepn F_81aac D_81aac.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_81ab0 D_81ab0.
    stepn F_81ab4 D_81ab4.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x79abc S top bot).
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
#[using="Type"] Lemma art_icu2_fn : forall regs (M rom : word -> option byte) (S n t f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x79b18 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 n -> cellA M (S - 2160) 8 (U (0x79abc : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  msteps ASEGS (mkst regs (0x81f98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x525b4 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2144))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 0x13c5d8)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 8)) 13 (Z_to_bv 64 (S - 2128))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 (U (0x79abc : bv 64)%bv))) 19 (Z_to_bv 64 1)) 20 (Z_to_bv 64 (S - 2128))) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x525e4 : word) (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x79b28 : bv 64)%bv)) (S - 2144) S) rom).
Proof.
  intros regs M rom S n t f22 f23 f24 H2 H24 HS HS' Hn Ht Ht' Atsp Hf22 Hf23 Hf24 W Wt C36 C44 C52 C60 C68 C76 C84 C92 C00 C08.
  zsb F_81b80 D_81b80 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x79b18) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 n) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x79abc : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_81b84 D_81b84 (S - 2136) D36. zld F_81b88 D_81b88 (S - 2144) D44. zld F_81b8c D_81b8c (S - 2152) D52. zld F_81b90 D_81b90 (S - 2160) D60.
  zld F_81b94 D_81b94 (S - 2168) D68. zld F_81b98 D_81b98 (S - 2176) D76. zld F_81b9c D_81b9c (S - 2184) D84. zld F_81ba0 D_81ba0 (S - 2192) D92.
  zld F_81ba4 D_81ba4 (S - 2200) D00. zld F_81ba8 D_81ba8 (S - 2208) D08.
  zstep F_81bac D_81bac.
  stepjr F_81bb0 D_81bb0 (0x79b18 : bv 64)%bv ltac:(gres; bveq).
  zstep F_79700 D_79700. zstep F_79704 D_79704. zstep F_79708 D_79708.
  stepn F_7970c D_7970c.
  zstep F_52170 D_52170.
  zsd F_52174 D_52174 (S - 2136) (U (0x79b28 : bv 64)%bv) ltac:(rewok W).
  zsd F_52178 D_52178 (S - 2144) S ltac:(rewok W).
  zstep F_5217c D_5217c. zstep F_52180 D_52180. zstep F_52184 D_52184. zstep F_52188 D_52188. zstep F_5218c D_5218c. zstep F_52190 D_52190. zstep F_52194 D_52194.
  stepn F_52198 D_52198.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic3_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S ub g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2144) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 (U (0x79b28 : bv 64)%bv) -> cellA M (S - 2144) 8 S ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x525b4 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) raw0 M rom).
Proof.
  intros regs M rom raw0 S ub g16 g24 g32 g40 g48 g56 H2 H10 Hub HS HS' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C36 C44 C8 C16 C24 C32 C40 C48 C56.
  zbft F_5219c D_5219c.
  zld F_521a0 D_521a0 (S - 2136) C36. zld F_521a4 D_521a4 (S - 2144) C44.
  zstep F_521a8 D_521a8.
  stepjr F_521ac D_521ac (0x79b28 : bv 64)%bv ltac:(gres; bveq).
  zstep F_79710 D_79710.
  zld F_79714 D_79714 (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_79718 D_79718 (S - 16) C16. zld F_7971c D_7971c (S - 24) C24. zld F_79720 D_79720 (S - 32) C32.
  zld F_79724 D_79724 (S - 40) C40. zld F_79728 D_79728 (S - 48) C48. zld F_7972c D_7972c (S - 56) C56.
  zstep F_79730 D_79730.
  stepret F_79734 D_79734 raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
