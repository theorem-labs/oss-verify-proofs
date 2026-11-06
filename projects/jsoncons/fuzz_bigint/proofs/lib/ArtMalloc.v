(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtLeaf ArtPoison ArtAllocG ArtUnwind.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_5fc54_604d4 As0_code_67d5c_67ecc As0_code_3d034_3dfbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_icu1 : forall regs (M rom : word -> option byte) (raw0 : word) (S n tp key tsd ctx t top bot : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 n ->
  0x10007fff8000 + 8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x633000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x633000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x633000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x633000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0xde818 1 1 -> cellA M 0xde83c 4 30 -> cellA M 0xd58a8 8 0x16f668 -> cellA M (0x16f668 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x5fe34 : word) M rom) (mkst regs1 (0x80834 : word) M1 rom)
    /\ getr regs1 1 = (0x67e98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x5fefc /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 8) 8 (U raw0) /\ cellA M1 (S - 16) 8 (U (getr regs 8)) /\ cellA M1 (S - 24) 8 (U (getr regs 9)) /\ cellA M1 (S - 32) 8 (U (getr regs 18))
    /\ cellA M1 (S - 40) 8 (U (getr regs 19)) /\ cellA M1 (S - 48) 8 (U (getr regs 20)) /\ cellA M1 (S - 56) 8 (U (getr regs 21))
    /\ cellA M1 (S - 2136) 8 0x5ff58 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 n /\ cellA M1 (S - 2160) 8 (U (0x5fefc : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
    /\ cellA M1 (S - 2176) 8 (S - 2128) /\ cellA M1 (S - 2184) 8 (S - 81)
    /\ cellA M1 (S - 2192) 8 (U (getr regs 22)) /\ cellA M1 (S - 2200) 8 (U (getr regs 23)) /\ cellA M1 (S - 2208) 8 (U (getr regs 24))
    /\ cellA M1 (S - 2128) 8 (S - 2112) /\ cellA M1 (S - 2120) 4 0 /\ cellA M1 (S - 2116) 4 0
    /\ wrA M1 (S - 4096) 4096.
Proof.
  intros regs M rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 HS HS' Hn Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
         W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  eexists _, _. split.
  - zstep F_5fe34 D_5fe34.
    zsd F_5fe38 D_5fe38 (S - 8) (U raw0) ltac:(rewok W). zsd F_5fe3c D_5fe3c (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5fe40 D_5fe40 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5fe44 D_5fe44 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5fe48 D_5fe48 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5fe4c D_5fe4c (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5fe50 D_5fe50 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_5fe54 D_5fe54. zstep F_5fe58 D_5fe58. zstep F_5fe5c D_5fe5c. zstep F_5fe60 D_5fe60.
    stepn F_5fe64 D_5fe64.
    zcall (art_try_init_fn _ _ _ _ (S - 2128)).
    zbft F_5fe68 D_5fe68.
    zstep F_5fe6c D_5fe6c. zstep F_5fe70 D_5fe70. zstep F_5fe74 D_5fe74. zstep F_5fe78 D_5fe78. zstep F_5fe7c D_5fe7c.
    zsd F_5fe80 D_5fe80 (S - 72) 0 ltac:(rewok W).
    zsd F_5fe84 D_5fe84 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_5fe88 D_5fe88 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_5fe8c D_5fe8c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_5fe90 D_5fe90.
    zbtk F_5fe94 D_5fe94.
    stepn F_5fef8 D_5fef8.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_5fefc D_5fefc.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0xd58a8 8 0x16f668) by zcell; assert (Cfast' : cellA X (0x16f668 + 34) 1 1) by zcell end.
    zld F_5ff00 D_5ff00 0xd58a8 Cg38'. zlbu F_5ff04 D_5ff04 (0x16f668 + 34) Cfast'.
    zstep F_5ff08 D_5ff08.
    stepn F_5ff0c D_5ff0c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_5ff10 D_5ff10. zstep F_5ff14 D_5ff14. zstep F_5ff18 D_5ff18.
    stepn F_5ff1c D_5ff1c. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_5ff20 D_5ff20.
    zsd F_5ff24 D_5ff24 (S - 72) S ltac:(rewok W).
    zbtk F_5ff28 D_5ff28.
    zstep F_5ff3c D_5ff3c. zstep F_5ff40 D_5ff40. zstep F_5ff44 D_5ff44. zstep F_5ff48 D_5ff48. zstep F_5ff4c D_5ff4c. zstep F_5ff50 D_5ff50.
    stepn F_5ff54 D_5ff54.
    (* [comment removed for export] *)
    zstep F_67d7c D_67d7c.
    zsd F_67d80 D_67d80 (S - 2136) 0x5ff58 ltac:(rewok W). zsd F_67d84 D_67d84 (S - 2144) S ltac:(rewok W). zsd F_67d88 D_67d88 (S - 2152) n ltac:(rewok W).
    zsd F_67d8c D_67d8c (S - 2160) (U (0x5fefc : bv 64)%bv) ltac:(rewok W). zsd F_67d90 D_67d90 (S - 2168) 1 ltac:(rewok W). zsd F_67d94 D_67d94 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_67d98 D_67d98 (S - 2184) (S - 81) ltac:(rewok W). zsd F_67d9c D_67d9c (S - 2192) (U (getr regs 22)) ltac:(rewok W).
    zsd F_67da0 D_67da0 (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd F_67da4 D_67da4 (S - 2208) (U (getr regs 24)) ltac:(rewok W).
    zstep F_67da8 D_67da8. zstep F_67dac D_67dac. zstep F_67db0 D_67db0. zstep F_67db4 D_67db4. zstep F_67db8 D_67db8. zstep F_67dbc D_67dbc.
    zsw F_67dc0 D_67dc0 (S - 2120) 0 ltac:(rewok W).
    stepn F_67dc4 D_67dc4.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_67dc8 D_67dc8.
    stepn F_67dcc D_67dcc.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x5fefc S top bot).
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
Lemma art_icu2_fn : forall regs (M rom : word -> option byte) (S n t f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) ->
  8192 <= S -> S <= 2 ^ 47 -> 0 <= n < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 ->
  0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 ->
  cellA M (S - 2136) 8 0x5ff58 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 n -> cellA M (S - 2160) 8 (U (0x5fefc : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  msteps ASEGS (mkst regs (0x67e98 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x3d340 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2144))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 0xda4d8)) 11 (Z_to_bv 64 n)) 12 (Z_to_bv 64 8)) 13 (Z_to_bv 64 (S - 2128))) 14 (Z_to_bv 64 1)) 15 (Z_to_bv 64 1)) 18 (Z_to_bv 64 (U (0x5fefc : bv 64)%bv))) 19 (Z_to_bv 64 1)) 20 (Z_to_bv 64 (S - 2128))) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x3d370 : word) (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x5ff68 : bv 64)%bv)) (S - 2144) S) rom).
Proof.
  intros regs M rom S n t f22 f23 f24 H2 H24 HS HS' Hn Ht Ht' Atsp Hf22 Hf23 Hf24 W Wt C36 C44 C52 C60 C68 C76 C84 C92 C00 C08.
  zsb F_67e98 D_67e98 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x5ff58) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 n) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x5fefc : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_67e9c D_67e9c (S - 2136) D36. zld F_67ea0 D_67ea0 (S - 2144) D44. zld F_67ea4 D_67ea4 (S - 2152) D52. zld F_67ea8 D_67ea8 (S - 2160) D60.
  zld F_67eac D_67eac (S - 2168) D68. zld F_67eb0 D_67eb0 (S - 2176) D76. zld F_67eb4 D_67eb4 (S - 2184) D84. zld F_67eb8 D_67eb8 (S - 2192) D92.
  zld F_67ebc D_67ebc (S - 2200) D00. zld F_67ec0 D_67ec0 (S - 2208) D08.
  zstep F_67ec4 D_67ec4.
  stepjr F_67ec8 D_67ec8 (0x5ff58 : bv 64)%bv ltac:(gres; bveq).
  zstep F_5ff58 D_5ff58. zstep F_5ff5c D_5ff5c. zstep F_5ff60 D_5ff60.
  stepn F_5ff64 D_5ff64.
  zstep F_3d314 D_3d314.
  zsd F_3d318 D_3d318 (S - 2136) (U (0x5ff68 : bv 64)%bv) ltac:(rewok W).
  zsd F_3d31c D_3d31c (S - 2144) S ltac:(rewok W).
  zstep F_3d320 D_3d320. zstep F_3d324 D_3d324. zstep F_3d328 D_3d328. zstep F_3d32c D_3d32c. zstep F_3d330 D_3d330. zstep F_3d334 D_3d334. zstep F_3d338 D_3d338.
  stepn F_3d33c D_3d33c.
  zret.
Qed.

(* [comment removed for export] *)
Lemma art_ic3_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S ub g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2144) -> getr regs 10 = Z_to_bv 64 ub -> 1 <= ub < 2 ^ 64 -> 8192 <= S -> S <= 2 ^ 47 -> ret_ok raw0 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (S - 2136) 8 (U (0x5ff68 : bv 64)%bv) -> cellA M (S - 2144) 8 S ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 ->
  cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x3d340 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) raw0 M rom).
Proof.
  intros regs M rom raw0 S ub g16 g24 g32 g40 g48 g56 H2 H10 Hub HS HS' Hret Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 C36 C44 C8 C16 C24 C32 C40 C48 C56.
  zbft F_3d340 D_3d340.
  zld F_3d344 D_3d344 (S - 2136) C36. zld F_3d348 D_3d348 (S - 2144) C44.
  zstep F_3d34c D_3d34c.
  stepjr F_3d350 D_3d350 (0x5ff68 : bv 64)%bv ltac:(gres; bveq).
  zstep F_5ff68 D_5ff68.
  zld F_5ff6c D_5ff6c (S - 8) C8. rewrite Z_to_bv_bv_unsigned.
  zld F_5ff70 D_5ff70 (S - 16) C16. zld F_5ff74 D_5ff74 (S - 24) C24. zld F_5ff78 D_5ff78 (S - 32) C32.
  zld F_5ff7c D_5ff7c (S - 40) C40. zld F_5ff80 D_5ff80 (S - 48) C48. zld F_5ff84 D_5ff84 (S - 56) C56.
  zstep F_5ff88 D_5ff88.
  stepret F_5ff8c D_5ff8c raw0 ltac:(rwH; reflexivity).
  zret.
Qed.
End FPX.
