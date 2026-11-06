(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac ArtLeaf ArtPoison ArtAllocG ArtUnwind ArtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_5fc54_604d4 As0_code_67d5c_67ecc As0_code_3d034_3dfbc As0_code_415bc_42aa8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fi_mem (M : word -> option byte) (S : Z) (raw0 : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (S - 8) (U raw0)) (S - 16) (U (getr regs 8))) (S - 24) (U (getr regs 9))) (S - 32) (U (getr regs 18))) (S - 40) (U (getr regs 19))) (S - 48) (U (getr regs 20))) (S - 56) (U (getr regs 21)).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma art_fi_a_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 10 = Z_to_bv 64 p ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 ->
  wrA M (S - 4096) 4096 ->
  msteps ASEGS (mkst regs (0x5fc64 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5fc98)) 2 (Z_to_bv 64 (S - 2128))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 p)) 18 raw0)
          (0x6b860 : word) (art_fi_mem M S raw0 regs) rom).
Proof.
  intros regs M rom raw0 S p H1 H2 H10 HS HS' Hp W.
    zstep F_5fc64 D_5fc64.
    zsd F_5fc68 D_5fc68 (S - 8) (U raw0) ltac:(rewok W). zsd F_5fc6c D_5fc6c (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5fc70 D_5fc70 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5fc74 D_5fc74 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5fc78 D_5fc78 (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5fc7c D_5fc7c (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5fc80 D_5fc80 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_5fc84 D_5fc84. zstep F_5fc88 D_5fc88. zstep F_5fc8c D_5fc8c. zstep F_5fc90 D_5fc90.
    stepn F_5fc94 D_5fc94.
    unfold art_fi_mem. zret.
Qed.
Lemma art_fi_b : forall regs (M rom : word -> option byte) (S p qp tp key tsd ctx t top bot : Z),
  getr regs 2 = Z_to_bv 64 (S - 2128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 S -> getr regs 9 = Z_to_bv 64 p -> getr regs 10 = Z_to_bv 64 0xded40 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 47 -> p = 2 ^ 32 * qp + p mod 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x633000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x633000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x633000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x633000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0xde818 1 1 -> cellA M 0xde83c 4 30 -> cellA M 0xd58a8 8 0x16f668 -> cellA M (0x16f668 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  cellA M (0xded40 + 8 + 8 * qp) 8 0 ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x5fc98 : word) M rom) (mkst regs1 (0x80834 : word) M1 rom)
    /\ getr regs1 1 = (0x67e98 : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x5fd9c /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S - 64) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 2136) 8 0x5fdf8 /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 p /\ cellA M1 (S - 2160) 8 (U (0x5fd9c : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
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
    stepn F_5fc98 D_5fc98. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
    zbft F_5fc9c D_5fc9c.
    stepn F_5fca0 D_5fca0. rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
    stepn F_5fca4 D_5fca4. rwH. rewrite art_zb_slli by lia.
    zstep F_5fca8 D_5fca8.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0xded40 + qp * 2 ^ 3 + 8) 8 0) by (replace (0xded40 + qp * 2 ^ 3 + 8) with (0xded40 + 8 + 8 * qp) by lia; recell Cmap) end.
    zld F_5fcac D_5fcac (0xded40 + qp * 2 ^ 3 + 8) Cmap'.
    stepfence F_5fcb0 D_5fcb0.
    zbtk F_5fcb4 D_5fcb4.
    (* [comment removed for export] *)
    zstep F_5fd3c D_5fd3c. zstep F_5fd40 D_5fd40. zstep F_5fd44 D_5fd44. zstep F_5fd48 D_5fd48. zstep F_5fd4c D_5fd4c.
    zsd F_5fd50 D_5fd50 (S - 72) 0 ltac:(rewok W).
    zsd F_5fd54 D_5fd54 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_5fd58 D_5fd58 (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_5fd5c D_5fd5c.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_5fd60 D_5fd60.
    zbtk F_5fd64 D_5fd64.
    stepn F_5fd98 D_5fd98.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_5fd9c D_5fd9c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0xd58a8 8 0x16f668) by zcell; assert (Cfast' : cellA X (0x16f668 + 34) 1 1) by zcell end.
    zld F_5fda0 D_5fda0 0xd58a8 Cg38'. zlbu F_5fda4 D_5fda4 (0x16f668 + 34) Cfast'.
    zstep F_5fda8 D_5fda8.
    stepn F_5fdac D_5fdac.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_5fdb0 D_5fdb0. zstep F_5fdb4 D_5fdb4. zstep F_5fdb8 D_5fdb8.
    stepn F_5fdbc D_5fdbc. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_5fdc0 D_5fdc0.
    zsd F_5fdc4 D_5fdc4 (S - 72) S ltac:(rewok W).
    zbtk F_5fdc8 D_5fdc8.
    zstep F_5fddc D_5fddc. zstep F_5fde0 D_5fde0. zstep F_5fde4 D_5fde4. zstep F_5fde8 D_5fde8. zstep F_5fdec D_5fdec. zstep F_5fdf0 D_5fdf0.
    stepn F_5fdf4 D_5fdf4.
    (* [comment removed for export] *)
    zstep F_67d7c D_67d7c.
    zsd F_67d80 D_67d80 (S - 2136) 0x5fdf8 ltac:(rewok W). zsd F_67d84 D_67d84 (S - 2144) S ltac:(rewok W). zsd F_67d88 D_67d88 (S - 2152) p ltac:(rewok W).
    zsd F_67d8c D_67d8c (S - 2160) (U (0x5fd9c : bv 64)%bv) ltac:(rewok W). zsd F_67d90 D_67d90 (S - 2168) 1 ltac:(rewok W). zsd F_67d94 D_67d94 (S - 2176) (S - 2128) ltac:(rewok W).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x5fd9c S top bot).
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
End FPX.
