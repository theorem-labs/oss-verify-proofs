(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_cb5 Z_tr_st4 Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac dsite_fin POSTNAME EX MU WM GA GD Gpend DEC LOW SIDE :=
  apply evt_done; unfold POSTNAME, utfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; EX;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|];
  first [ split; [LOW|]; SIDE; split; [reflexivity| lia] | LOW ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfb_d1_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z)
    (ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a3 a4 a7 w m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV0) (wz 65535) a3 a4 w (wz BV) a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c928) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV0) /\ bv_unsigned w mod 2^16 = BB mod 2^16.

Lemma tfb_d1 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= last <= 1 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) -> 0 <= mb <= 18 ->
  evt usegs (tfb_d1_post L s sp last len bufp mb (sbF_PB PB PD BB BV (4 + last) 3) (sbF_PD PD BV 3) (sbF_BB BB BV (4 + last) 3) BV (sbF_BV BV 3)
                ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c7e0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY Rl RBV RPD ROOM Rmb. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  zs2. zs2. zs2. zs2. zs2. rewrite slt_lxor by lia. replace (last + 4 <? last) with false by (symmetry; apply Z.ltb_ge; lia). reg_as (last + 4) (4 + last).
 
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. zs. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zstep. zs2.
    dsite_fin tfb_d1_post ltac:(do 5 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(idtac).
  - (* [comment removed for export] *)
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (4 + last)) by lia. zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. zs. sb_or w LO BB (rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1c850 TF_TRAP. at_pc 0x1c850.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (4 + last)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1c884 TF_TRAP. at_pc 0x1c884.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (4 + last)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (4 + last))) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1c8a8 TF_TRAP. at_pc 0x1c8a8.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range (4 + last) (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. zstep. br_true. reg_as (BV + -13) (BV + 3 - 16).
    dsite_fin tfb_d1_post ltac:(do 5 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(idtac).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfb_d2_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a3 a7 w pcx m',
    ms' = MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz mb) (wz (ds_l_max_code s + 1)) (wz 65535) a3 w (wz 12) (wz BV) a7
                (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cbe8 /\ BV <= 11) \/ (pcx = 0x1ca2c /\ 12 <= BV)).

Lemma tfb_d2 : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp mb : Z) (PB : arr) (PD BB BV0 BV : Z) (w : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a3 a4 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD w (wz BV0) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  rw_cells usegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  256 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 0 <= BV <= 16 -> 0 <= PD -> (11 < BV -> PD + 2 <= 65536) ->
  evt usegs (tfb_d2_post L s sp last bufp mb (sbF_PB PB PD BB BV (ds_l_max_code s - 256) 5) (sbF_PD PD BV 5) (sbF_BB BB BV (ds_l_max_code s - 256) 5) (sbF_BV BV 5)
                ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV0) (wz 65535) a3 a4 w (wz BV) a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c928) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY GB Rlm Rdm RBV RPD ROOM. unfold utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH. unfold dsB_cells in GB.
  zs2. zs2. zstep. ustep TF_TRAP. zs2. zs2. ustep TF_TRAP. clear GB. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2.
  change (Z.lxor (Z.b2z true) 1) with 0. replace (ds_l_max_code s + -256) with (ds_l_max_code s - 256) by lia.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs. zs. sb_or w1 LO BB (exact HW).
    zstep. zs2. zstep. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2. change (Z.lxor (Z.b2z true) 1) with 0.
    reg_as (ds_d_max_code s + 1 + -1) (ds_d_max_code s).
    zstep. br_cases K2.
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(right).
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 5) BV)) by lia) ltac:(exact LO) ltac:(left).
  - (* [comment removed for export] *)
    ustep TF_TRAP. zs2. ustep TF_TRAP. zs2. rewrite (land16_small (ds_l_max_code s - 256)) by lia.
    zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1c9ac TF_TRAP. at_pc 0x1c9ac.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (ds_l_max_code s - 256)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1c9e0 TF_TRAP. at_pc 0x1c9e0.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (ds_l_max_code s - 256)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (ds_l_max_code s - 256))) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1ca04 TF_TRAP. at_pc 0x1ca04.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range (ds_l_max_code s - 256) (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. ustep TF_TRAP. zstep. zs2. zs2. rewrite slt_lxor by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. zs2. zs2. change (Z.lxor (Z.b2z true) 1) with 0.
    reg_as (ds_d_max_code s + 1 + -1) (ds_d_max_code s). reg_as (BV + -11) (BV + 5 - 16).
    zstep. br_cases K2.
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
    + dsite_fin tfb_d2_post ltac:(do 7 eexists) MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 5) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
Qed.
