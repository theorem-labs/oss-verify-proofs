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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3cf10_3de98_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_alloc_rodata (M : word -> option byte) : Prop :=
  cellA M 0x10438 8 0x218a392cd3d5dbf /\ cellA M 0x104bc 1 3 /\ cellA M 0x10360 8 0xcc6e96b9cc6e96b9.

(* [comment removed for export] *)
Definition art_alloc_memA1 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 128 + 120) (U raw)) (sp - 128 + 112) (U (getr regs 8))) (sp - 128 + 104) (U (getr regs 9))) (sp - 128 + 96) (U (getr regs 18))) (sp - 128 + 88) (U (getr regs 19))) (sp - 128 + 80) (U (getr regs 20))) (sp - 128 + 72) (U (getr regs 21))) (sp - 128 + 64) (U (getr regs 22))) (sp - 128 + 56) (U (getr regs 23))) (sp - 128 + 48) (U (getr regs 24))) (sp - 128 + 40) (U (getr regs 25))) (sp - 128 + 32) (U (getr regs 26))) (sp - 128 + 24) (U (getr regs 27))) (sp - 128 + 8) 1) (sp - 128 + 16) 16).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_alloc_a1_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia n stk : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 n ->
  getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  256 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 < 2 ^ 64 -> 1 <= stk < 2 ^ 64 -> 1 <= n < 2 ^ 40 ->
  wrA M (sp - 256) 256 -> 0x696000 + 256 <= sp ->
  art_alloc_rodata M -> cellA M 0x140918 1 1 -> cellA M 0x1c1ea2 1 0 ->
  msteps ASEGS (mkst regs (0x525e4 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52640 : bv 64)%bv) 2 (Z_to_bv 64 (sp - 128))) 8 (Z_to_bv 64 8)) 9 (Z_to_bv 64 1)) 10 (Z_to_bv 64 49)) 11 (Z_to_bv 64 16)) 12 (Z_to_bv 64 0x104b8)) 13 (Z_to_bv 64 (2 ^ 64 - 8))) 18 (Z_to_bv 64 8)) 21 (Z_to_bv 64 n)) 22 (Z_to_bv 64 ia)) 23 (Z_to_bv 64 stk)) 25 (Z_to_bv 64 7)) 26 (Z_to_bv 64 (ia + 2047))) 27 (Z_to_bv 64 1)) (0x5267c : word) (art_alloc_memA1 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hia Hia' Hstk Hn W IMG (R1 & R2 & R3) Ci Cr.
  zstep F_521cc D_521cc.
  zsd F_521d0 D_521d0 (sp - 128 + 120) (U raw) ltac:(rewok W).
  zsd F_521d4 D_521d4 (sp - 128 + 112) (U (getr regs 8)) ltac:(rewok W).
  zsd F_521d8 D_521d8 (sp - 128 + 104) (U (getr regs 9)) ltac:(rewok W).
  zsd F_521dc D_521dc (sp - 128 + 96) (U (getr regs 18)) ltac:(rewok W).
  zsd F_521e0 D_521e0 (sp - 128 + 88) (U (getr regs 19)) ltac:(rewok W).
  zsd F_521e4 D_521e4 (sp - 128 + 80) (U (getr regs 20)) ltac:(rewok W).
  zsd F_521e8 D_521e8 (sp - 128 + 72) (U (getr regs 21)) ltac:(rewok W).
  zsd F_521ec D_521ec (sp - 128 + 64) (U (getr regs 22)) ltac:(rewok W).
  zsd F_521f0 D_521f0 (sp - 128 + 56) (U (getr regs 23)) ltac:(rewok W).
  zsd F_521f4 D_521f4 (sp - 128 + 48) (U (getr regs 24)) ltac:(rewok W).
  zsd F_521f8 D_521f8 (sp - 128 + 40) (U (getr regs 25)) ltac:(rewok W).
  zsd F_521fc D_521fc (sp - 128 + 32) (U (getr regs 26)) ltac:(rewok W).
  zsd F_52200 D_52200 (sp - 128 + 24) (U (getr regs 27)) ltac:(rewok W).
  zstep F_52204 D_52204. zstep F_52208 D_52208. zstep F_5220c D_5220c. zstep F_52210 D_52210. zstep F_52214 D_52214. zstep F_52218 D_52218.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
  assert (Ci' : cellA Mf 0x140918 1 1) by (unfold Mf; unfold apart in *; recell Ci).
  assert (Cr' : cellA Mf 0x1c1ea2 1 0) by (unfold Mf; unfold apart in *; recell Cr).
  assert (R1' : cellA Mf 0x10438 8 0x218a392cd3d5dbf) by (unfold Mf; unfold apart in *; recell R1).
  assert (R2' : cellA Mf 0x104bc 1 3) by (unfold Mf; unfold apart in *; recell R2).
  stepn F_5221c D_5221c.
  zcall (art_asan_inited_fn _ _ _ _).
  zbft F_52220 D_52220.
  stepn F_52224 D_52224.
  zcall (art_rss_limit_fn _ _ _ _).
  zbft F_52228 D_52228.
  zbft F_5222c D_5222c.
  zstep F_52230 D_52230.
  zbtk F_52234 D_52234.
  zstep F_52270 D_52270. zstep F_52274 D_52274.
  zbtk F_52278 D_52278.
  zstep F_52280 D_52280. zstep F_52284 D_52284.
  zbft F_52288 D_52288.
  zstep F_5228c D_5228c. zld F_52290 D_52290 0x10438 R1'.
  zstep F_52294 D_52294. zstep F_52298 D_52298. zstep F_5229c D_5229c. zstep F_522a0 D_522a0. zstep F_522a4 D_522a4. zstep F_522a8 D_522a8.
  zstep F_522ac D_522ac.
  zlbu F_522b0 D_522b0 0x104bc R2'.
  zstep F_522b4 D_522b4. zstep F_522b8 D_522b8. zstep F_522bc D_522bc. zstep F_522c0 D_522c0.
  zbtk F_522c4 D_522c4.
  zstep F_52244 D_52244. zstep F_52248 D_52248. zstep F_5224c D_5224c.
  zbft F_52250 D_52250.
  zstep F_52254 D_52254. zstep F_52258 D_52258.
  zsd F_5225c D_5225c (sp - 128 + 8) 1 ltac:(unfold Mf; rewok W).
  zsd F_52260 D_52260 (sp - 128 + 16) 16 ltac:(unfold Mf; rewok W).
  unfold Mf, art_alloc_memA1. zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_ladder : forall regs (M rom : word -> option byte) (n : Z),
  getr regs 10 = Z_to_bv 64 49 -> getr regs 21 = Z_to_bv 64 n -> 1 <= n < 2 ^ 40 ->
  exists regs',
    msteps ASEGS (mkst regs (0x5267c : word) M rom) (mkst regs' (0x52750 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (AsanTab.rz_log n)
    /\ (forall r : reg, r <> 10%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom n H10 H21 Hn.
  unfold AsanTab.rz_log.
  destruct (Z.le_gt_cases n 48) as [C0|C0'].
  { eexists. split; [|split]; [ zbft F_52264 D_52264; zstep F_52268 D_52268; stepn F_5226c D_5226c; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 96) as [C1|C1'].
  { eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbft F_522d0 D_522d0; zstep F_522d4 D_522d4; stepn F_522d8 D_522d8; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 448) as [C2|C2'].
  { eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbtk F_522d0 D_522d0; zstep F_522dc D_522dc; zbft F_522e0 D_522e0; zstep F_522e4 D_522e4;
      stepn F_522e8 D_522e8; apply mst_refl | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 3968) as [C3|C3'].
  { eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbtk F_522d0 D_522d0; zstep F_522dc D_522dc; zbtk F_522e0 D_522e0;
      zstep F_522ec D_522ec; zstep F_522f0 D_522f0; zbft F_522f4 D_522f4; zstep F_522f8 D_522f8; stepn F_522fc D_522fc; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 16128) as [C4|C4'].
  { eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbtk F_522d0 D_522d0; zstep F_522dc D_522dc; zbtk F_522e0 D_522e0;
      zstep F_522ec D_522ec; zstep F_522f0 D_522f0; zbtk F_522f4 D_522f4; zstep F_52300 D_52300; zstep F_52304 D_52304; zbft F_52308 D_52308;
      zstep F_5230c D_5230c; stepn F_52310 D_52310; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  destruct (Z.le_gt_cases n 32256) as [C5|C5'].
  { eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbtk F_522d0 D_522d0; zstep F_522dc D_522dc; zbtk F_522e0 D_522e0;
      zstep F_522ec D_522ec; zstep F_522f0 D_522f0; zbtk F_522f4 D_522f4; zstep F_52300 D_52300; zstep F_52304 D_52304; zbtk F_52308 D_52308;
      zstep F_52314 D_52314; zstep F_52318 D_52318; zbft F_5231c D_5231c; zstep F_52320 D_52320; stepn F_52324 D_52324; apply mst_refl
    | gres; zif; reflexivity | intros; kept_solve ]. }
  (* [comment removed for export] *)
  eexists. split; [|split]; [ zbtk F_52264 D_52264; zstep F_522cc D_522cc; zbtk F_522d0 D_522d0; zstep F_522dc D_522dc; zbtk F_522e0 D_522e0;
      zstep F_522ec D_522ec; zstep F_522f0 D_522f0; zbtk F_522f4 D_522f4; zstep F_52300 D_52300; zstep F_52304 D_52304; zbtk F_52308 D_52308;
      zstep F_52314 D_52314; zstep F_52318 D_52318; zbtk F_5231c D_5231c; zstep F_52328 D_52328; zstep F_5232c D_5232c; zstep F_52330 D_52330;
      zstep F_52334 D_52334; apply mst_refl
    | gres | intros; kept_solve ].
  destruct (Z.le_gt_cases n 64512) as [C6|C6']; zif; vals_lit; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_a2_fn : forall regs (M rom : word -> option byte) (sp ia : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x696000 ->
  wrA M (sp - 16) 16 -> 0x696000 + 16 <= sp ->
  art_rz_rodata M -> cellA M (ia + 3624) 2 16 -> cellA M (ia + 3626) 2 2048 ->
  msteps ASEGS (mkst regs (0x52750 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x5277c : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 7)) 11 (Z_to_bv 64 7)) 12 (Z_to_bv 64 11)) 13 (Z_to_bv 64 2048)) 14 (Z_to_bv 64 2048)) 20 (Z_to_bv 64 65536)) 24 (Z_to_bv 64 65535)) (0x5277c : word) (Wn 8 (Wn 8 M (sp - 8) 0x52768) (sp - 8) 0x5277c) rom).
Proof.
  intros regs M rom sp ia H2 H26 Hsp Hsp' Hia Hia' W IMG RO Cmin Cmax.
  zlh F_52338 D_52338 (ia + 3624) Cmin.
  stepfence F_5233c D_5233c.
  zstep F_52340 D_52340. zstep F_52344 D_52344. zstep F_52348 D_52348.
  stepn F_5234c D_5234c.
  zcall (art_rz2log_16_fn _ _ _ sp _).
  zstep F_52350 D_52350.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmax' : cellA X (ia + 3626) 2 2048) by (unfold apart in *; recell Cmax) end.
  zlh F_52354 D_52354 (ia + 3626) Cmax'.
  stepfence F_52358 D_52358.
  zstep F_5235c D_5235c.
  stepn F_52360 D_52360.
  zcall (art_rz2log_2048_fn _ _ _ sp _).
  { destruct RO as (R1 & R2 & R3). unfold art_rz_rodata. repeat split; recell R1 || recell R2 || recell R3. }
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_clamp : forall regs (M rom : word -> option byte) (n r : Z),
  getr regs 9 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 7 -> getr regs 19 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 n ->
  1 <= n < 2 ^ 40 -> r = AsanTab.rz_log n ->
  exists regs',
    msteps ASEGS (mkst regs (0x5277c : word) M rom) (mkst regs' (0x52798 : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 (Z.max n 8) /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 19 = Z_to_bv 64 r
    /\ (forall x : reg, x <> 10%bv -> x <> 11%bv -> x <> 19%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom n r H9 H10 H19 H21 Hn Hr.
  pose proof (AsanTab.rz_log_range n) as Rr. rewrite <- Hr in Rr.
  assert (CASES : r = 0 \/ (0 < r < 7) \/ r = 7) by lia.
  assert (Rlo : 0 < r -> 49 <= n).
  { intros Hp. destruct (Z.le_gt_cases n 48) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
    replace (n <=? 48) with true in Hp by (symmetry; apply Z.leb_le; lia). lia. }
  assert (R7 : r = 7 -> 64513 <= n).
  { intros Hp. destruct (Z.le_gt_cases n 64512) as [L|G]; [exfalso|lia]. subst r. unfold AsanTab.rz_log in Hp.
    repeat (lazymatch type of Hp with context [if ?c then _ else _] => destruct c eqn:?; [lia|] end).
    repeat match goal with H : (_ <=? _) = false |- _ => apply Z.leb_gt in H; revert H end. lia. }
  destruct CASES as [R0 | [RM | RS]].
  - destruct (Z.le_gt_cases n 8) as [S|B].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_52364 D_52364; zstep F_52368 D_52368; zbft F_5236c D_5236c; zstep F_52370 D_52370; zstep F_52374 D_52374; zbft F_52378 D_52378; zstep F_5237c D_5237c; apply mst_refl
        | gres; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
    + eexists. split; [|split; [|split; [|split]]];
        [ zbft F_52364 D_52364; zstep F_52368 D_52368; zbft F_5236c D_5236c; zstep F_52370 D_52370; zstep F_52374 D_52374; zbtk F_52378 D_52378; apply mst_refl
        | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
  - specialize (Rlo ltac:(lia)).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_52364 D_52364; zbtk F_52410 D_52410; zstep F_52370 D_52370; zstep F_52374 D_52374; zbtk F_52378 D_52378; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; reflexivity | intros; kept_solve ].
  - specialize (R7 RS).
    eexists. split; [|split; [|split; [|split]]];
      [ zbtk F_52364 D_52364; zbft F_52410 D_52410; zstep F_52414 D_52414; zstep F_52418 D_52418; zstep F_5241c D_5241c; zbft F_52420 D_52420;
        stepn F_52424 D_52424; apply mst_refl
      | gres; rwH; f_equal; lia | gres; reflexivity | gres; rwH; f_equal; lia | intros; kept_solve ].
Qed.

#[using="Type"] Lemma art_zb_sllw_small : forall x k, 0 <= x -> 0 <= k < 32 -> x * 2 ^ k < 2 ^ 31 ->
  v_sllw (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (x * 2 ^ k).
Proof.
  intros x k Hx Hk Hxk. unfold v_sllw.
  assert (Hx' : x < 2 ^ 31). { pose proof (Z.pow_pos_nonneg 2 k). nia. }
  rewrite !art_u_lit by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  pose proof (Z.pow_pos_nonneg 2 k). rewrite Z.mod_small by nia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_alloc_a3_fn : forall regs (M rom : word -> option byte) (sp ia n r rs rz tp key tsd ctx t : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 8 -> getr regs 10 = Z_to_bv 64 (Z.max n 8) ->
  getr regs 18 = Z_to_bv 64 8 -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 65536 -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 22 = Z_to_bv 64 ia -> getr regs 26 = Z_to_bv 64 (ia + 2047) ->
  16 <= sp -> sp < 2 ^ 64 -> 4096 <= ia -> ia + 4096 <= 0x696000 -> 0x696000 + 16 <= sp ->
  1 <= n < 2 ^ 40 -> 0 <= r <= 7 -> rs = (Z.max n 8 + 7) / 8 * 8 -> rz = 16 * 2 ^ r -> rs + rz <= 65536 ->
  wrA M (sp - 16) 16 -> cellA M (ia + 3616) 8 (2 ^ 40) -> art_tsd M tp key tsd ctx t -> 1 <= t ->
  apart (sp - 16) 16 (tp - 88) 8 -> apart (sp - 16) 16 (tsd + 8 * key) 8 -> apart (sp - 16) 16 (ctx + 152) 8 ->
  msteps ASEGS (mkst regs (0x52798 : word) M rom)
               (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x52884 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 1)) 9 (Z_to_bv 64 n)) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (t + 208))) 12 (Z_to_bv 64 (rs + rz))) 13 (Z_to_bv 64 8)) 19 (Z_to_bv 64 (rs + rz))) 20 (Z_to_bv 64 rz)) 24 (Z_to_bv 64 (2 ^ 64 - 8))) 26 (Z_to_bv 64 t)) (0x56d3c : word) (Wn 8 M (sp - 8) 0x52868) rom).
Proof.
  intros regs M rom sp ia n r rs rz tp key tsd ctx t H2 H4 H8 H10 H18 H19 H20 H21 H22 H26 Hsp Hsp' Hia Hia' IMG Hn Hr Hrs Hrz Hprim W Cmax TSD Ht A1 A2 A3.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  assert (Hrs8 : rs mod 8 = 0) by (subst rs; apply Z_mod_mult).
  assert (Hrslo : 8 <= rs). { subst rs. pose proof (Z.mul_succ_div_gt (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mul_div_le (Z.max n 8 + 7) 8 ltac:(lia)). lia. } assert (Hrz16 : 16 <= rz <= 2048) by (subst rz; split; [|change 2048 with (16 * 2 ^ 7); apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]]; pose proof (Z.pow_pos_nonneg 2 r); nia).
  zstep F_52380 D_52380. zstep F_52384 D_52384. zstep F_52388 D_52388. zstep F_5238c D_5238c. zstep F_52390 D_52390.
  stepn F_52394 D_52394. rwH. rewrite art_zb_and by lia. rewrite art_land_m8 by lia.
  match goal with |- context [Z_to_bv 64 (?e / 8 * 8)] => replace (e / 8 * 8) with rs by (rewrite Hrs; f_equal; f_equal; lia) end.
  zstep F_52398 D_52398. zstep F_5239c D_5239c.
  stepn F_523a0 D_523a0. rwH. rewrite art_zb_andi by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite Hrs8.
  zbft F_523a4 D_523a4.
  zstep F_523a8 D_523a8. zstep F_523ac D_523ac. zstep F_523b0 D_523b0.
  stepn F_523b4 D_523b4. rwH. rewrite art_zb_sllw_small by (subst rz; lia). rewrite <- Hrz.
  zstep F_523b8 D_523b8. zstep F_523bc D_523bc. zstep F_523c0 D_523c0. zstep F_523c4 D_523c4. zstep F_523c8 D_523c8. zstep F_523cc D_523cc.
  zstep F_523d0 D_523d0.
  stepn F_523d4 D_523d4. rwH. rewrite art_zb_and by lia. rewrite Z.land_0_l.
  zstep F_523d8 D_523d8. zstep F_523dc D_523dc.
  zbft F_523e0 D_523e0. zbft F_523e4 D_523e4.
  zld F_523e8 D_523e8 (ia + 3616) Cmax.
  zbtk F_523ec D_523ec.
  stepn F_5244c D_5244c.
  zcall (art_cur_thread_fn _ _ _ _ sp tp key tsd ctx t).
  zbft F_52454 D_52454 || (zstep F_52450 D_52450; zbft F_52454 D_52454).
  zstep F_52458 D_52458. zstep F_5245c D_5245c. zstep F_52460 D_52460. zstep F_52464 D_52464.
  stepn F_52468 D_52468.
  zret.
Qed.
End FPX.
