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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac EbtLeaf EbtPoison EbtAllocG EbtUnwind EbtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r5fac4_60344 Eb0_code_r67bcc_67d3c Eb0_code_r3cf10_3de98 Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fi_mem (M : word -> option byte) (S : Z) (raw0 : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (S - 8) (U raw0)) (S - 16) (U (getr regs 8))) (S - 24) (U (getr regs 9))) (S - 32) (U (getr regs 18))) (S - 40) (U (getr regs 19))) (S - 48) (U (getr regs 20))) (S - 56) (U (getr regs 21)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_fi_a_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 10 = Z_to_bv 64 p ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 ->
  wrA M (S - 4096) 4096 ->
  msteps ASEGS (mkst regs (0x7a9d0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x7aa04)) 2 (Z_to_bv 64 (S - 2128))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 p)) 18 raw0)
          (0x86b0c : word) (art_fi_mem M S raw0 regs) rom).
Proof.
  intros regs M rom raw0 S p H1 H2 H10 HS HS' Hp W.
    zstep F_7a980 D_7a980.
    zsd F_7a984 D_7a984 (S - 8) (U raw0) ltac:(rewok W). zsd F_7a988 D_7a988 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_7a98c D_7a98c (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7a990 D_7a990 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_7a994 D_7a994 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_7a998 D_7a998 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_7a99c D_7a99c (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_7a9a0 D_7a9a0. zstep F_7a9a4 D_7a9a4. zstep F_7a9a8 D_7a9a8. zstep F_7a9ac D_7a9ac.
    stepn F_7a9b0 D_7a9b0.
    unfold art_fi_mem. zret.
Qed.
#[using="Type"] Lemma art_fi_b : forall regs (M rom : word -> option byte) (S p qp tp key tsd ctx t top bot : Z),
  getr regs 2 = Z_to_bv 64 (S - 2128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 S -> getr regs 9 = Z_to_bv 64 p -> getr regs 10 = Z_to_bv 64 0x147300 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 47 -> p = 2 ^ 32 * qp + p mod 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x69c000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x69c000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x69c000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x69c000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x146dd8 1 1 -> cellA M 0x146dfc 4 30 -> cellA M 0x13d8b8 8 0x1d7c28 -> cellA M (0x1d7c28 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  cellA M (0x147300 + 8 + 8 * qp) 8 0 ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x7aa04 : word) M rom) (mkst regs1 (0x9bafc : word) M1 rom)
    /\ getr regs1 1 = (0x83144 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x7ab08 /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S - 64) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 2136) 8 0x7ab64 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 p /\ cellA M1 (S - 2160) 8 (U (0x7ab08 : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
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

    stepn F_7a9b4 D_7a9b4. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
    zbft F_7a9b8 D_7a9b8.
    stepn F_7a9bc D_7a9bc. rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
    stepn F_7a9c0 D_7a9c0. rwH. rewrite art_zb_slli by lia.
    zstep F_7a9c4 D_7a9c4.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0x147300 + qp * 2 ^ 3 + 8) 8 0) by (replace (0x147300 + qp * 2 ^ 3 + 8) with (0x147300 + 8 + 8 * qp) by lia; recell Cmap) end.
    zld F_7a9c8 D_7a9c8 (0x147300 + qp * 2 ^ 3 + 8) Cmap'.
    stepfence F_7a9cc D_7a9cc.
    zbtk F_7a9d0 D_7a9d0.

    zstep F_7aa58 D_7aa58. zstep F_7aa5c D_7aa5c. zstep F_7aa60 D_7aa60. zstep F_7aa64 D_7aa64. zstep F_7aa68 D_7aa68.
    zsd F_7aa6c D_7aa6c (S - 72) 0 ltac:(rewok W).
    zsd F_7aa70 D_7aa70 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_7aa74 D_7aa74 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_7aa78 D_7aa78.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7aa7c D_7aa7c.
    zbtk F_7aa80 D_7aa80.
    stepn F_7aab4 D_7aab4.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_7aab8 D_7aab8.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x13d8b8 8 0x1d7c28) by zcell; assert (Cfast' : cellA X (0x1d7c28 + 34) 1 1) by zcell end.
    zld F_7aabc D_7aabc 0x13d8b8 Cg38'. zlbu F_7aac0 D_7aac0 (0x1d7c28 + 34) Cfast'.
    zstep F_7aac4 D_7aac4.
    stepn F_7aac8 D_7aac8.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7aacc D_7aacc. zstep F_7aad0 D_7aad0. zstep F_7aad4 D_7aad4.
    stepn F_7aad8 D_7aad8. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_7aadc D_7aadc.
    zsd F_7aae0 D_7aae0 (S - 72) S ltac:(rewok W).
    zbtk F_7aae4 D_7aae4.
    zstep F_7aaf8 D_7aaf8. zstep F_7aafc D_7aafc. zstep F_7ab00 D_7ab00. zstep F_7ab04 D_7ab04. zstep F_7ab08 D_7ab08. zstep F_7ab0c D_7ab0c.
    stepn F_7ab10 D_7ab10.

    zstep F_82fd8 D_82fd8.
    zsd F_82fdc D_82fdc (S - 2136) 0x7ab64 ltac:(rewok W). zsd F_82fe0 D_82fe0 (S - 2144) S ltac:(rewok W). zsd F_82fe4 D_82fe4 (S - 2152) p ltac:(rewok W).
    zsd F_82fe8 D_82fe8 (S - 2160) (U (0x7ab08 : bv 64)%bv) ltac:(rewok W). zsd F_82fec D_82fec (S - 2168) 1 ltac:(rewok W). zsd F_82ff0 D_82ff0 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_82ff4 D_82ff4 (S - 2184) (S - 81) ltac:(rewok W). zsd F_82ff8 D_82ff8 (S - 2192) (U (getr regs 22)) ltac:(rewok W).
    zsd F_82ffc D_82ffc (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd F_83000 D_83000 (S - 2208) (U (getr regs 24)) ltac:(rewok W).
    zstep F_83004 D_83004. zstep F_83008 D_83008. zstep F_8300c D_8300c. zstep F_83010 D_83010. zstep F_83014 D_83014. zstep F_83018 D_83018.
    zsw F_8301c D_8301c (S - 2120) 0 ltac:(rewok W).
    stepn F_83020 D_83020.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_83024 D_83024.
    stepn F_83028 D_83028.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x7ab08 S top bot).
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
