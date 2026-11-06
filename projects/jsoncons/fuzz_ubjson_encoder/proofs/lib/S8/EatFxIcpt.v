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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac EatLeaf EatPoison EatAllocG EatUnwind EatFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r5fac4_60344 Ea0_code_r67bcc_67d3c Ea0_code_r3cf10_3de98 Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_fi_mem (M : word -> option byte) (S : Z) (raw0 : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (S - 8) (U raw0)) (S - 16) (U (getr regs 8))) (S - 24) (U (getr regs 9))) (S - 32) (U (getr regs 18))) (S - 40) (U (getr regs 19))) (S - 48) (U (getr regs 20))) (S - 56) (U (getr regs 21)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_fi_a_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p : Z),
  getr regs 1 = raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 10 = Z_to_bv 64 p ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 ->
  wrA M (S - 4096) 4096 ->
  msteps ASEGS (mkst regs (0x7a1a8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x7a1dc)) 2 (Z_to_bv 64 (S - 2128))) 8 (Z_to_bv 64 S)) 9 (Z_to_bv 64 p)) 18 raw0)
          (0x862e4 : word) (art_fi_mem M S raw0 regs) rom).
Proof.
  intros regs M rom raw0 S p H1 H2 H10 HS HS' Hp W.
    zstep F_7a158 D_7a158.
    zsd F_7a15c D_7a15c (S - 8) (U raw0) ltac:(rewok W). zsd F_7a160 D_7a160 (S - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_7a164 D_7a164 (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_7a168 D_7a168 (S - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_7a16c D_7a16c (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_7a170 D_7a170 (S - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_7a174 D_7a174 (S - 56) (U (getr regs 21)) ltac:(rewok W).
    zstep F_7a178 D_7a178. zstep F_7a17c D_7a17c. zstep F_7a180 D_7a180. zstep F_7a184 D_7a184.
    stepn F_7a188 D_7a188.
    unfold art_fi_mem. zret.
Qed.
#[using="Type"] Lemma art_fi_b : forall regs (M rom : word -> option byte) (S p qp tp key tsd ctx t top bot : Z),
  getr regs 2 = Z_to_bv 64 (S - 2128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 S -> getr regs 9 = Z_to_bv 64 p -> getr regs 10 = Z_to_bv 64 0x142c00 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 47 -> p = 2 ^ 32 * qp + p mod 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> hid (t + 4096 <= 0x10000 \/ 0x698000 <= t) -> apart t 4096 (S - 4096) 8192 ->
  apart ctx 4096 (S - 4096) 8192 -> hid (ctx + 4096 <= 0x10000 \/ 0x698000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x698000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x698000 -> 0 <= bot < top -> top < 2 ^ 63 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> art_tsd M tp key tsd ctx t ->
  cellA M 0x1426d8 1 1 -> cellA M 0x1426fc 4 30 -> cellA M 0x1391a8 8 0x1d3528 -> cellA M (0x1d3528 + 34) 1 1 ->
  cellA M (t + 3168) 1 0 -> cellA M (t + 40) 1 0 -> cellA M (t + 8) 8 top -> cellA M (t + 16) 8 bot ->
  cellA M (0x142c00 + 8 + 8 * qp) 8 0 ->
  exists regs1 M1,
    msteps ASEGS (mkst regs (0x7a1dc : word) M rom) (mkst regs1 (0x9b2d4 : word) M1 rom)
    /\ getr regs1 1 = (0x8291c : bv 64)%bv /\ getr regs1 2 = Z_to_bv 64 (S - 2208) /\ getr regs1 10 = Z_to_bv 64 (S - 2128)
    /\ getr regs1 11 = Z_to_bv 64 0x7a2e0 /\ getr regs1 12 = Z_to_bv 64 S /\ getr regs1 13 = Z_to_bv 64 top /\ getr regs1 14 = Z_to_bv 64 bot
    /\ getr regs1 15 = Z_to_bv 64 30 /\ getr regs1 24 = Z_to_bv 64 (t + 2047) /\ getr regs1 4 = Z_to_bv 64 tp
    /\ (forall r : reg, In r [3; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
    /\ mem_grows M M1
    /\ (forall x : word, ~ (S - 2272 <= U x < S - 64) -> U x <> t + 3168 -> M1 x = M x)
    /\ cellA M1 (S - 2136) 8 0x7a33c /\ cellA M1 (S - 2144) 8 S /\ cellA M1 (S - 2152) 8 p /\ cellA M1 (S - 2160) 8 (U (0x7a2e0 : bv 64)%bv) /\ cellA M1 (S - 2168) 8 1
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

    stepn F_7a18c D_7a18c. rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
    zbft F_7a190 D_7a190.
    stepn F_7a194 D_7a194. rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
    stepn F_7a198 D_7a198. rwH. rewrite art_zb_slli by lia.
    zstep F_7a19c D_7a19c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0x142c00 + qp * 2 ^ 3 + 8) 8 0) by (replace (0x142c00 + qp * 2 ^ 3 + 8) with (0x142c00 + 8 + 8 * qp) by lia; recell Cmap) end.
    zld F_7a1a0 D_7a1a0 (0x142c00 + qp * 2 ^ 3 + 8) Cmap'.
    stepfence F_7a1a4 D_7a1a4.
    zbtk F_7a1a8 D_7a1a8.

    zstep F_7a230 D_7a230. zstep F_7a234 D_7a234. zstep F_7a238 D_7a238. zstep F_7a23c D_7a23c. zstep F_7a240 D_7a240.
    zsd F_7a244 D_7a244 (S - 72) 0 ltac:(rewok W).
    zsd F_7a248 D_7a248 (S - 2128) (S - 2112) ltac:(rewok W).
    zsd F_7a24c D_7a24c (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
    stepn F_7a250 D_7a250.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7a254 D_7a254.
    zbtk F_7a258 D_7a258.
    stepn F_7a28c D_7a28c.
    zcall (art_get_pc_fn _ _ _ _).
    zstep F_7a290 D_7a290.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x1391a8 8 0x1d3528) by zcell; assert (Cfast' : cellA X (0x1d3528 + 34) 1 1) by zcell end.
    zld F_7a294 D_7a294 0x1391a8 Cg38'. zlbu F_7a298 D_7a298 (0x1d3528 + 34) Cfast'.
    zstep F_7a29c D_7a29c.
    stepn F_7a2a0 D_7a2a0.
    zcall (art_malloc_ctx_fn _ _ _ _).
    zstep F_7a2a4 D_7a2a4. zstep F_7a2a8 D_7a2a8. zstep F_7a2ac D_7a2ac.
    stepn F_7a2b0 D_7a2b0. rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
    zstep F_7a2b4 D_7a2b4.
    zsd F_7a2b8 D_7a2b8 (S - 72) S ltac:(rewok W).
    zbtk F_7a2bc D_7a2bc.
    zstep F_7a2d0 D_7a2d0. zstep F_7a2d4 D_7a2d4. zstep F_7a2d8 D_7a2d8. zstep F_7a2dc D_7a2dc. zstep F_7a2e0 D_7a2e0. zstep F_7a2e4 D_7a2e4.
    stepn F_7a2e8 D_7a2e8.

    zstep F_827b0 D_827b0.
    zsd F_827b4 D_827b4 (S - 2136) 0x7a33c ltac:(rewok W). zsd F_827b8 D_827b8 (S - 2144) S ltac:(rewok W). zsd F_827bc D_827bc (S - 2152) p ltac:(rewok W).
    zsd F_827c0 D_827c0 (S - 2160) (U (0x7a2e0 : bv 64)%bv) ltac:(rewok W). zsd F_827c4 D_827c4 (S - 2168) 1 ltac:(rewok W). zsd F_827c8 D_827c8 (S - 2176) (S - 2128) ltac:(rewok W).
    zsd F_827cc D_827cc (S - 2184) (S - 81) ltac:(rewok W). zsd F_827d0 D_827d0 (S - 2192) (U (getr regs 22)) ltac:(rewok W).
    zsd F_827d4 D_827d4 (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd F_827d8 D_827d8 (S - 2208) (U (getr regs 24)) ltac:(rewok W).
    zstep F_827dc D_827dc. zstep F_827e0 D_827e0. zstep F_827e4 D_827e4. zstep F_827e8 D_827e8. zstep F_827ec D_827ec. zstep F_827f0 D_827f0.
    zsw F_827f4 D_827f4 (S - 2120) 0 ltac:(rewok W).
    stepn F_827f8 D_827f8.
    zcall (art_asan_inited_fn _ _ _ _).
    zbft F_827fc D_827fc.
    stepn F_82800 D_82800.
    zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
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
    zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x7a2e0 S top bot).
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
