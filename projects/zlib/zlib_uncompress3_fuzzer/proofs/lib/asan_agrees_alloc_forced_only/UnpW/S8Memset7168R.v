(* (uncompress 1.4): memset(d, 0, 7168): the opening steps (memset304_run's, offsets moved) and
   the whole run, over S8Memset7168's loop. Split from S8Memset7168.v (one file went over 300 s). *)

Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.GcF06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.S8_code_20000_20a98 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.S8Memset OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.S8Memset7168.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac gfin := gres; pin; first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.PropExec.FPState}.

Definition memset7168_ws_pro : list (Z * nat) :=
  [(0,1%nat); (7167,1%nat); (1,1%nat); (2,1%nat); (7165,1%nat); (7166,1%nat); (3,1%nat); (7164,1%nat);
   (0,4%nat); (7164,4%nat); (4,4%nat); (8,4%nat); (7156,4%nat); (7160,4%nat); (12,4%nat); (16,4%nat); (20,4%nat);
   (24,4%nat); (7140,4%nat); (7144,4%nat); (7148,4%nat); (7152,4%nat)]%Z.
Definition memset7168_ws : list (Z * nat) := memset7168_ws_pro ++ [(24%Z, (32 * 223)%nat)].

Lemma memset7168_ws_inb : ws_inb memset7168_ws 7168 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset7168_ws_cover : ws_cover memset7168_ws 7168 = true.
Proof. vm_compute. reflexivity. Qed.

(* memset's opening steps for n = 7168 (memset304_run's, offsets moved), up to the loop head *)
Lemma memset7168_pro : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7168 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok SEGS mem d (7 * 1024) = true ->
  exists regs1 mem1,
    msteps SEGS (mkst regs (0x20638 : word) mem rom) (mkst regs1 (0x20710 : word) mem1 rom)
    /\ mem1 = zstores mem d memset7168_ws_pro
    /\ getr regs1 1 = ret
    /\ getr regs1 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat 223))
    /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 13 = Z_to_bv 64 31
    /\ getr regs1 14 = Z_to_bv 64 (32 * Z.of_nat 223 + 8)
    /\ regs_agree (fun r => In r memset_clob) regs regs1.
Proof.
  intros regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - stepb_ft F_204c0 D_204c0 ltac:(pin; cond_compute).
    stw F_204c4 D_204c4 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_204c8 D_204c8 (Z_to_bv 64 (bv_unsigned d + 7168)).
    sn F_204cc D_204cc.
    stw F_204d0 D_204d0 (Z_to_bv 64 (bv_unsigned d + 7167)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204d4 D_204d4 ltac:(pin; cond_compute).
    stw F_204d8 D_204d8 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204dc D_204dc (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_204e0 D_204e0.
    stw F_204e4 D_204e4 (Z_to_bv 64 (bv_unsigned d + 7165)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_204e8 D_204e8 (Z_to_bv 64 (bv_unsigned d + 7166)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204ec D_204ec ltac:(pin; cond_compute).
    stw F_204f0 D_204f0 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_204f4 D_204f4.
    stw F_204f8 D_204f8 (Z_to_bv 64 (bv_unsigned d + 7164)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_204fc D_204fc ltac:(pin; cond_compute).
    sn F_20500 D_20500.
    sn F_20504 D_20504.
    sn F_20508 D_20508.
    stepiv F_2050c D_2050c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_20510 D_20510.
    sn F_20514 D_20514.
    sv F_20518 D_20518 (d).
    sn F_2051c D_2051c.
    sn F_20520 D_20520.
    sn F_20524 D_20524.
    stw F_20528 D_20528 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_2052c D_2052c (Z_to_bv 64 (bv_unsigned d + 7168)).
    stw F_20530 D_20530 (Z_to_bv 64 (bv_unsigned d + 7164)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20534 D_20534 ltac:(pin; cond_compute).
    stw F_20538 D_20538 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2053c D_2053c (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_20540 D_20540.
    stw F_20544 D_20544 (Z_to_bv 64 (bv_unsigned d + 7156)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20548 D_20548 (Z_to_bv 64 (bv_unsigned d + 7160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2054c D_2054c ltac:(pin; cond_compute).
    stw F_20550 D_20550 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20554 D_20554 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20558 D_20558 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2055c D_2055c (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_20560 D_20560 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_20564 D_20564.
    sn F_20568 D_20568.
    sn F_2056c D_2056c.
    stw F_20570 D_20570 (Z_to_bv 64 (bv_unsigned d + 7140)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 7144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 7148)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 7152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_20580 D_20580 ltac:(pin; cond_compute).
    sn F_20584 D_20584.
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_2058c D_2058c.
    sn F_20590 D_20590.
    sn F_20594 D_20594.
    OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - reflexivity.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - unfold memset_clob. solve_regs_agree.
Qed.

Theorem memset7168_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7168 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok SEGS mem d (7 * 1024) = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x20638 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 7168)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  destruct (memset7168_pro regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok)
    as (r1 & m1 & RUN1 & EQ1 & G1 & G11 & G12 & G13 & G14 & AG1).
  destruct (memset7168_loop 223 r1 m1 rom d ret ltac:(lia) ltac:(lia) G1 Hret G11 G12 G13 G14 Hnw)
    as (r2 & m2 & RUN2 & EQ2 & AG2).
  { subst m1. unfold memset7168_ws_pro. cbn [zstores]. ok_sub Hok. }
  exists r2, m2. split; [eapply msteps_trans; eassumption|]. split; [| eapply regs_agree_trans; eassumption].
  rewrite EQ2, EQ1.
  rewrite <- (zstores_cover d 7168 Hnw memset7168_ws mem 7168%nat eq_refl memset7168_ws_inb memset7168_ws_cover).
  unfold memset7168_ws. rewrite zstores_app. cbn [zstores].
  replace (7160 - 32 * Z.of_nat 223)%Z with 24%Z by lia. reflexivity.
Qed.
End FXG.
