(* memset(d, 0, 7176) at 0x218b0. Below, the plain text: memset(d, 0, 7168): the opening steps (memset304_run's, offsets moved) and
   the whole run, over S9Memset7168's loop. Split from S9Memset7168.v (one file went over 300 s). *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* memset(d, 0, 7176) at 0x21820. Below, the plain text: memset(d, 0, 7168): the opening steps (memset304_run's, offsets moved) and
   the whole run, over S9Memset7168's loop. Split from S9Memset7168.v (one file went over 300 s). *)

Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.GcF06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac U7_code_21000_21d00 U7Memset U7Memset7176.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac gfin := gres; pin; first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].

Definition memset7176_ws_pro : list (Z * nat) :=
  [(0,1%nat); (7175,1%nat); (1,1%nat); (2,1%nat); (7173,1%nat); (7174,1%nat); (3,1%nat); (7172,1%nat);
   (0,4%nat); (7172,4%nat); (4,4%nat); (8,4%nat); (7164,4%nat); (7168,4%nat); (12,4%nat); (16,4%nat); (20,4%nat);
   (24,4%nat); (7148,4%nat); (7152,4%nat); (7156,4%nat); (7160,4%nat)]%Z.
Definition memset7176_ws : list (Z * nat) := memset7176_ws_pro ++ [(24%Z, (32 * 223)%nat)].

Lemma memset7176_ws_inb : ws_inb memset7176_ws 7176 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma memset7176_ws_cover : ws_cover memset7176_ws 7176 = true.
Proof. vm_compute. reflexivity. Qed.

(* memset's opening steps for n = 7168 (memset304_run's, offsets moved), up to the loop head *)
Lemma memset7176_pro {RCa1 : RunCtx}  : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7176 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7176 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem d (7 * 1024 + 8) = true ->
  exists regs1 mem1,
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x21874 : word) mem rom) (mkst regs1 (0x2194c : word) mem1 rom)
    /\ mem1 = zstores mem d memset7176_ws_pro
    /\ getr regs1 1 = ret
    /\ getr regs1 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat 223))
    /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 13 = Z_to_bv 64 31
    /\ getr regs1 14 = Z_to_bv 64 (32 * Z.of_nat 223 + 16)
    /\ regs_agree (fun r => In r memset_clob) regs regs1.
Proof.
  intros regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - stepb_ft F_21728 D_21728 ltac:(pin; cond_compute).
    stw F_2172c D_2172c (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_21730 D_21730 (Z_to_bv 64 (bv_unsigned d + 7176)).
    sn F_21734 D_21734.
    stw F_21738 D_21738 (Z_to_bv 64 (bv_unsigned d + 7175)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2173c D_2173c ltac:(pin; cond_compute).
    stw F_21740 D_21740 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21744 D_21744 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_21748 D_21748.
    stw F_2174c D_2174c (Z_to_bv 64 (bv_unsigned d + 7173)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_21750 D_21750 (Z_to_bv 64 (bv_unsigned d + 7174)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_21754 D_21754 ltac:(pin; cond_compute).
    stw F_21758 D_21758 (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_2175c D_2175c.
    stw F_21760 D_21760 (Z_to_bv 64 (bv_unsigned d + 7172)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_21764 D_21764 ltac:(pin; cond_compute).
    sn F_21768 D_21768.
    sn F_2176c D_2176c.
    sn F_21770 D_21770.
    stepiv F_21774 D_21774 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_21778 D_21778.
    sn F_2177c D_2177c.
    sv F_21780 D_21780 (d).
    sn F_21784 D_21784.
    sn F_21788 D_21788.
    sn F_2178c D_2178c.
    stw F_21790 D_21790 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_21794 D_21794 (Z_to_bv 64 (bv_unsigned d + 7176)).
    stw F_21798 D_21798 (Z_to_bv 64 (bv_unsigned d + 7172)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_2179c D_2179c ltac:(pin; cond_compute).
    stw F_217a0 D_217a0 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217a4 D_217a4 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_217a8 D_217a8.
    stw F_217ac D_217ac (Z_to_bv 64 (bv_unsigned d + 7164)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217b0 D_217b0 (Z_to_bv 64 (bv_unsigned d + 7168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_217b4 D_217b4 ltac:(pin; cond_compute).
    stw F_217b8 D_217b8 (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217bc D_217bc (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217c0 D_217c0 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217c4 D_217c4 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_217c8 D_217c8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_217cc D_217cc.
    sn F_217d0 D_217d0.
    sn F_217d4 D_217d4.
    stw F_217d8 D_217d8 (Z_to_bv 64 (bv_unsigned d + 7148)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217dc D_217dc (Z_to_bv 64 (bv_unsigned d + 7152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217e0 D_217e0 (Z_to_bv 64 (bv_unsigned d + 7156)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_217e4 D_217e4 (Z_to_bv 64 (bv_unsigned d + 7160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_217e8 D_217e8 ltac:(pin; cond_compute).
    sn F_217ec D_217ec.
    sv F_217f0 D_217f0 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_217f4 D_217f4.
    sn F_217f8 D_217f8.
    sn F_217fc D_217fc.
    OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - reflexivity.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - gfin.
  - unfold memset_clob. solve_regs_agree.
Qed.

Theorem memset7176_run {RCa1 : RunCtx}  : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 7176 ->
  (bv_unsigned d mod 8 = 0)%Z -> (bv_unsigned d + 7176 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem d (7 * 1024 + 8) = true ->
  exists regs' mem',
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x21874 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 7176)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  destruct (memset7176_pro regs mem rom d ret Hra Hd H11 H12 Hal Hnw Hok)
    as (r1 & m1 & RUN1 & EQ1 & G1 & G11 & G12 & G13 & G14 & AG1).
  destruct (memset7176_loop 223 r1 m1 rom d ret ltac:(lia) ltac:(lia) G1 Hret G11 G12 G13 G14 Hnw)
    as (r2 & m2 & RUN2 & EQ2 & AG2).
  { subst m1. unfold memset7176_ws_pro. cbn [zstores]. ok_sub Hok. }
  exists r2, m2. split; [eapply msteps_trans; eassumption|]. split; [| eapply regs_agree_trans; eassumption].
  rewrite EQ2, EQ1.
  rewrite <- (zstores_cover d 7176 Hnw memset7176_ws mem 7176%nat eq_refl memset7176_ws_inb memset7176_ws_cover).
  unfold memset7176_ws. rewrite zstores_app. cbn [zstores].
  replace (7160 - 32 * Z.of_nat 223)%Z with 24%Z by lia. reflexivity.
Qed.
