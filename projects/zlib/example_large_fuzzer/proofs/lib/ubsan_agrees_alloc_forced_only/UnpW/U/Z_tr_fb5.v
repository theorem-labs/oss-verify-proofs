(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_cb5 Z_tr_st4 Z_tr_fb1 Z_tr_fb4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfb_d3_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a7 w pcx m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cc14 /\ BV <= 12) \/ (pcx = 0x1caf8 /\ 13 <= BV)).

Lemma tfb_d3k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a3 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 11 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt usegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1cbe8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
  zstep. zs2. zstep. zs2. zs2.
  zstep. br_cases K2.
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(right).
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(left).
Qed.

Lemma tfb_d3f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a3 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 12 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt usegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1ca2c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (ds_d_max_code s)) by lia.
  zs2. zs2. shl_g0. ustep TF_TRAP.
  zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
  zs. zs. zstep. zs.
  uwalk 0x1ca80 TF_TRAP. at_pc 0x1ca80.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (ds_d_max_code s)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1cab4 TF_TRAP. at_pc 0x1cab4.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (ds_d_max_code s)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (ds_d_max_code s))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1cad8 TF_TRAP. at_pc 0x1cad8.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (ds_d_max_code s) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. ustep TF_TRAP. zstep. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16).
  zstep. br_cases K2.
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
  - dsite_fin tfb_d3_post ltac:(do 6 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfb_d4_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a3 a4 a5 a6 a7 w m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz (mb + 1)) (wz (ds_l_max_code s + 1)) a2 a3 a4 a5 a6 a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1cc34) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d4k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 12 -> 0 <= PD -> 3 <= mb <= 18 ->
  evt usegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) (sbF_BV BV 4)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1cc14) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. replace (mb + -3) with (mb - 3) by lia.
  zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
  zstep. zs2. zs2. zstep.
  dsite_fin tfb_d4_post ltac:(do 8 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 4) BV)) by lia) ltac:(exact LO) ltac:(idtac).
Qed.

Lemma tfb_d4f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 13 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 3 <= mb <= 18 ->
  evt usegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) (sbF_BV BV 4)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) w (wz (mb + -3)) (wz 13) (wz BV) a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1caf8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rlm Rdm RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. replace (mb + -3) with (mb - 3) by lia.
  zs2. ustep TF_TRAP. zs2. rewrite (land16_small (mb - 3)) by lia.
  zs2. zs2. shl_g0. ustep TF_TRAP.
  zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
  zs. zs. zstep. zs.
  uwalk 0x1cb48 TF_TRAP. at_pc 0x1cb48.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (mb - 3)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1cb7c TF_TRAP. at_pc 0x1cb7c.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (mb - 3)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (mb - 3))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1cba0 TF_TRAP. at_pc 0x1cba0.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (mb - 3) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. br_true. zs2. zstep. reg_as (BV + -12) (BV + 4 - 16).
  dsite_fin tfb_d4_post ltac:(do 8 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 4) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(idtac).
Qed.
