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
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatAllocG_b BatUnwind_b BatFree1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r5fac4_60344_b Ba0_code_r67bcc_67d3c_b Ba0_code_r3cf10_3de98_b Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fi_mem (M : word -> option byte) (S : Z) (raw0 : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (S - 8) (U raw0)) (S - 16) (U (getr regs 8))) (S - 24) (U (getr regs 9))) (S - 32) (U (getr regs 18))) (S - 40) (U (getr regs 19))) (S - 48) (U (getr regs 20))) (S - 56) (U (getr regs 21)).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_fi_a_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 10 = Z_to_bv 64 p ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 ->
  wrA M (S - 4096) 4096 ->
  msteps ASEGS (mkst regs (0x79824 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x79858)) 2 (Z_to_bv 64 (S - 2128))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 p)) 18 raw0)
          (0x85960 : word) (art_fi_mem M S raw0 regs) rom).
Proof.
  intros regs M rom raw0 S p H1 H2 H10 HS HS' Hp W.
    zstep F_7940c D_7940c.
    zsd F_79410 D_79410 (S - 8) (U raw0) ltac:(rewok W). zsd F_79414 D_79414 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_79418 D_79418 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7941c D_7941c (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_79420 D_79420 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_79424 D_79424 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_79428 D_79428 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_7942c D_7942c. zstep F_79430 D_79430. zstep F_79434 D_79434. zstep F_79438 D_79438.
    stepn F_7943c D_7943c.
    unfold art_fi_mem. zret.
Qed.
#[using="Type"] Lemma art_fi_b : forall regs (M rom : word -> option byte) (S p qp tp key tsd ctx t top bot : Z),
  getr regs 2 = Z_to_bv 64 (S - 2128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 S -> getr regs 9 = Z_to_bv 64 p -> getr regs 10 = Z_to_bv 64 0x140e40 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 47 -> p = 2 ^ 32 * qp + p mod 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x140918 1 1 -> cellA M 0x14093c 4 30 -> cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  cellA M (0x140e40 + 8 + 8 * qp) 8 0 ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x79858 : word) M rom) (mkst regs1 (0x9a950 : word) M1 rom)
    /\ getr regs1 1 = (0x81f98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x7995c /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S - 64) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 2136) 8 0x799b8 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 p /\ cellA M1 (S - 2160) 8 (U (0x7995c : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
    /\ cellA M1 (S - 2176) 8 (S - 2128) /\ cellA M1 (S - 2184) 8 (S - 81)
    /\ cellA M1 (S - 2192) 8 (U (getr regs 22)) /\ cellA M1 (S - 2200) 8 (U (getr regs 23)) /\ cellA M1 (S - 2208) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2128) 8 (S - 2112) /\ cellA M1 (S - 2120) 4 0 /\ cellA M1 (S - 2116) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom S p qp tp key tsd ctx t top bot H2 H4 H8 H9 H10 HS HS' Hp Eqp Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16 Cmap.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  assert (Hqp : 0 <= qp < 2 ^ 15) by (pose proof (Z.mod_pos_bound p (2 ^ 32) ltac:(lia)); lia).
  assert (Hqp' : p / 2 ^ 32 = qp). { symmetry. apply (Z.div_unique_pos _ (2 ^ 32) qp (p mod 2 ^ 32)); [pose proof (Z.mod_pos_bound p (2 ^ 32)); lia|lia]. }
  eexists _, _. split.
  -
    (* [comment removed for export] *)
    stepn F_79440 D_79440. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
    zbft F_79444 D_79444.
    stepn F_79448 D_79448. rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
    stepn F_7944c D_7944c. rwH. rewrite art_zb_slli by lia.
    zstep F_79450 D_79450.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0x140e40 + qp * 2 ^ 3 + 8) 8 0) by (replace (0x140e40 + qp * 2 ^ 3 + 8) with (0x140e40 + 8 + 8 * qp) by lia; recell Cmap) end.
    zld F_79454 D_79454 (0x140e40 + qp * 2 ^ 3 + 8) Cmap'.
    stepfence F_79458 D_79458.
    zbtk F_7945c D_7945c.
    (* [comment removed for export] *)
    zstep F_794e4 D_794e4. zstep F_794e8 D_794e8. zstep F_794ec D_794ec. zstep F_794f0 D_794f0. zstep F_794f4 D_794f4.
    zsd F_794f8 D_794f8 (S - 72) 0 ltac:(rewok W).
    zsd F_794fc D_794fc (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_79500 D_79500 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_79504 D_79504.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_79508 D_79508.
    zbtk F_7950c D_7950c.
    stepn F_79540 D_79540.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_79544 D_79544.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x1374b0 8 0x1d1768) by zcell; assert (Cfast' : cellA X (0x1d1768 + 34) 1 1) by zcell end.
    zld F_79548 D_79548 0x1374b0 Cg38'. zlbu F_7954c D_7954c (0x1d1768 + 34) Cfast'.
    zstep F_79550 D_79550.
    stepn F_79554 D_79554.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_79558 D_79558. zstep F_7955c D_7955c. zstep F_79560 D_79560.
    stepn F_79564 D_79564. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_79568 D_79568.
    zsd F_7956c D_7956c (S - 72) S ltac:(rewok W).
    zbtk F_79570 D_79570.
    zstep F_79584 D_79584. zstep F_79588 D_79588. zstep F_7958c D_7958c. zstep F_79590 D_79590. zstep F_79594 D_79594. zstep F_79598 D_79598.
    stepn F_7959c D_7959c.
    (* [comment removed for export] *)
    zstep F_81a64 D_81a64.
    zsd F_81a68 D_81a68 (S - 2136) 0x799b8 ltac:(rewok W). zsd F_81a6c D_81a6c (S - 2144) S ltac:(rewok W). zsd F_81a70 D_81a70 (S - 2152) p ltac:(rewok W).
    zsd F_81a74 D_81a74 (S - 2160) (U (0x7995c : bv 64)%bv) ltac:(rewok W). zsd F_81a78 D_81a78 (S - 2168) 1 ltac:(rewok W). zsd F_81a7c D_81a7c (S - 2176) (S - 2128) ltac:(rewok W).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x7995c S top bot).
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
End FPX.
