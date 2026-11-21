(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st4 Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition tfb_d1_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a2 a4 a6 wcell w m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) a2 w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b8fc) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d1 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_d1_post L s sp last len bufp mb (sbF_PB PB PD BB BV (4 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (4 + last) 3) BV (sbF_BV BV 3)
                ra gp tp t0 t1 t2 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) a1 (wz BV) a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b838) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. reg_as (last + 4) (4 + last). zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB). zs2.
    apply evt_done. unfold tfb_d1_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 6 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| exact LO].
  - (* [comment removed for export] *)
    zs2. zs2. zs2. zs2. zs2. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    sbf_b0 L Gpend PB PD (nbv BB BV (4 + last)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (4 + last)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
    zs2. zs2. reg_as (BV + -13) (BV + 3 - 16).
    apply evt_done. unfold tfb_d1_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 6 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.

(* [comment removed for export] *)
Definition tfb_d2_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a6 a7 wcell w pcx m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1b97c /\ BV < 12) \/ (pcx = 0x1b9c8 /\ 12 <= BV)).

Lemma lmax_eqm : forall lmax, (65535 + lmax - 255) mod 2^16 = (lmax - 256) mod 2^16.
Proof. intros. replace (65535 + lmax - 255) with (lmax - 256 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Ltac d2_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_d2_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; RW; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_d2 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z) (wcell w : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  rw_cells psegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  0 <= ds_l_max_code s < 2^31 -> 0 <= ds_d_max_code s < 2^31 -> 0 <= BV <= 16 -> 0 <= PD -> (11 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_d2_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_l_max_code s - 256) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_l_max_code s - 256) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) a2 w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b8fc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY GB Rlm Rdm RBV RPD ROOM. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (lmax_eqm (ds_l_max_code s)) as EQV.
  lay_open LAY. open_EM EMH. unfold dsB_cells in GB.
  zs2. zs2. zs2. clear GB. zs2. zs2. zs2. reg_as (65535 + ds_l_max_code s + -255) (65535 + ds_l_max_code s - 255).
  zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
    zs2. zs2. zs2.
    zstep. br_cases K2.
    + d2_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
    + d2_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  - (* [comment removed for export] *)
    zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
    sbf_b0 L Gpend PB PD (nbv BB BV (ds_l_max_code s - 256)) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV (ds_l_max_code s - 256)) LO.
    zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia. rewrite (wrap16_eqm16 _ _ EQV).
    zs2. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16).
    zstep. br_cases K2.
    + d2_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
    + d2_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

(* [comment removed for export] *)
Definition tfb_d3_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a4 a6 wcell w pcx m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1b9a0 /\ BV < 13) \/ (pcx = 0x1ba38 /\ 13 <= BV)).

Ltac d3_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_d3_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; RW; do 6 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_d3k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s < 2^31 -> 0 <= BV < 12 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt psegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b97c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rdm RBV RPD Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. sb_or w1 LO BB (exact HW).
  zs2. zs2. zs2. zs2. zs2. zs2. reg_as (65535 + mb + -2) (65535 + mb - 2).
  zstep. br_cases K2.
  - d3_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  - d3_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
Qed.

Lemma tfb_d3f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= ds_d_max_code s < 2^31 -> 12 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt psegs (tfb_d3_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_d_max_code s) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_d_max_code s) 5) (sbF_BV BV 5)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz BV) a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b9c8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY Rdm RBV RPD ROOM Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW).
  sbf_b0 L Gpend PB PD (nbv BB BV (ds_d_max_code s)) LO.
  sbf_b1 L Gpend GD PB PD (nbv BB BV (ds_d_max_code s)) LO.
  zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia.
  zs2. zs2. zs2. zs2. zs2. zs2. reg_as (BV + -11) (BV + 5 - 16). reg_as (65535 + mb + -2) (65535 + mb - 2).
  zstep. br_cases K2.
  - d3_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
  - d3_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

(* [comment removed for export] *)
Definition tfb_d4_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a3 a4 a6 wcell w m',
    ms' = MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 a0 w (wz (ds_l_max_code s)) a3 a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1ba90) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wcell (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma mb_eqm : forall mb, (65535 + mb - 2) mod 2^16 = (mb - 3) mod 2^16.
Proof. intros. replace (65535 + mb - 2) with (mb - 3 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Lemma tfb_d4k : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  0 <= BV < 13 -> 0 <= PD -> 0 <= mb <= 18 ->
  evt psegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) BV (sbF_BV BV 4)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1b9a0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (mb_eqm mb) as EQV.
  zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
  zs2. zs2.
  apply evt_done. unfold tfb_d4_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact EMH| exact LO].
Qed.

Lemma tfb_d4f : forall (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 a4 a6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  13 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= mb <= 18 ->
  evt psegs (tfb_d4_post L s sp last bufp mb (sbF_PB PB PD BB BV (mb - 3) 4) (sbF_PD PD BV 4) (sbF_BB BB BV (mb - 3) 4) BV (sbF_BV BV 4)
                ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (65535 + mb - 2)) (wz 65535) (wz (ds_l_max_code s)) w a4 (wz (mb + 1)) a6 (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1ba38) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rmb. unfold tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (mb_eqm mb) as EQV.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV _ _ EQV) in LO.
  sbf_b0 L Gpend PB PD (nbv BB BV (mb - 3)) LO.
  sbf_b1 L Gpend GD PB PD (nbv BB BV (mb - 3)) LO.
  zs2. zs2. zs2. zs2. zs2. rewrite srlw_val by lia. rewrite (wrap16_eqm16 _ _ EQV).
  zs2. reg_as (BV + -12) (BV + 4 - 16).
  apply evt_done. unfold tfb_d4_post, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV. rewrite !(proj2 (Z.ltb_lt _ _)) by lia. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [close_EM GA GD Gpend| apply lo16_unsigned_wz].
Qed.
