(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_env Fz_K_hash Fz_K_rep Fz_I2_ppis Fz_K_pstw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SITE_ppi_name : Z := 0x20ab30.
Definition SITE_ppi_val1 : Z := 0x20ab5c.
Definition SITE_ppi_val2 : Z := 0x20ab74.
Definition PPI_TAB : Z := 0x52f2e0.
Definition PPI_TAB_SH : Z := 0x8009de5c.
Definition A_PROVIDER : Z := 0x4b660. Definition A_VERSION : Z := 0x4b680. Definition A_FIPS : Z := 0x4b6a0. Definition A_OUTPUT : Z := 0x4b6c0.
Definition A_INPUT : Z := 0x4b6e0. Definition A_STRUCTURE : Z := 0x4b700. Definition A_YES : Z := 0x4b720. Definition A_NO : Z := 0x4b740.

(* [comment removed for export] *)
Definition ppi_fr (j : list byte) (s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 8 j; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
(* [comment removed for export] *)
Definition ppi_ent (site : Z) (sp gp tp t0 t1 t2 : word) (nmf lit : Z) (a4 a5 a6 a7 : word) (s2z s3z s4z : Z) (s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m' : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 site) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 nmf) (Z_to_bv 64 1) (Z_to_bv 64 lit) a4 a5 a6 a7
          (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 e_property_string) fc None m' (seg_rom asegs).

(* [comment removed for export] *)
Lemma ppi_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m PPI_TAB_SH [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = ppi_ent SITE_ppi_name sp gp tp t0 t1 t2 1 A_PROVIDER a4 a5 a6 a7 0 PPI_TAB PPI_TAB_SH s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) (ppi_fr j s5 s4 s3 s2 s1 s0 ra)
       /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PPI_CTX) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_property_parse_init) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC TSH MI. unfold e_property_parse_init, g_shadow_memory_dynamic_address, PPI_TAB_SH, PPI_CTX in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP)]) by sh_fp_lia.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. do 11 zstep.
  zstep. zsh. zstep. th_if_lit.
  do 4 zstep.
  th_frame 16%nat [8; 8]%nat ST.
  zstep. zstep; lfix. do 6 zstep.
  lazymatch goal with FRh : rw_cells _ _ (SP + -80) _ |- _ => th_release FRh (SP + -64) end.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ppi_ent, ppi_fr, SITE_ppi_name, A_PROVIDER, PPI_TAB, PPI_TAB_SH, PPI_CTX, e_property_string. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition ppi_ret (site : Z) (sp gp tp t0 t1 t2 : word) (res : Z) (a1 a2 a3 a4 a5 a6 a7 : word) (s2z s3z s4z : Z) (s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 site) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 PPI_CTX) (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 s2z) (Z_to_bv 64 s3z) (Z_to_bv 64 s4z) (Z_to_bv 64 (-48)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 site) fc None m (seg_rom asegs).
(* [comment removed for export] *)
Definition ppi_mid_post (site : Z) (sp gp tp t0 t1 t2 : word) (nmf lit : Z) (a4 a5 a6 a7 : word) (s2z s3z s4z : Z) (s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
       ms = ppi_ent site sp gp tp t0 t1 t2 nmf lit a4 a5 a6 a7 s2z s3z s4z s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m'
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp - 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp + -64).


Ltac is_zlit a := lazymatch a with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac ppi_norm := repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] => is_zlit a; is_zlit b; let v := eval vm_compute in (a + b) in change (a + b) with v end.
(* [comment removed for export] *)
Ltac ppi_wrap SP ST :=
  th_frame 16%nat [8; 8]%nat ST;
  zstep; (zstep; lfix); do 6 zstep;
  lazymatch goal with FRh : rw_cells _ _ (SP + -80) _ |- _ => th_release FRh (SP + -64) end;
  zstep; zstep.
Ltac ppi_mid_done SP :=
  subst SP; rewrite ?Z_to_bv_bv_unsigned;
  unfold ppi_mid_post, ppi_ent, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, A_VERSION, A_FIPS, A_OUTPUT, A_INPUT, A_STRUCTURE, A_YES, A_NO, PPI_TAB, PPI_TAB_SH, PPI_CTX, e_property_string;
  apply evt_done; eexists; split; [reflexivity|];
  split; [assumption|]; split; [assumption|]; split; [assumption| assumption].
(* [comment removed for export] *)
Ltac ppi_loop SP ST :=
  zstep; th_if_lit; do 4 zstep; th_if_lit;
  zstep; zsh; zstep; th_if_lit;
  do 4 zstep;
  ppi_wrap SP ST.

(* [comment removed for export] *)
Lemma ppi_w1 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m (PPI_TAB_SH + 1) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_name sp gp tp t0 t1 t2 1 A_VERSION a4 a5 a6 a7 (-8) (PPI_TAB + 8) (PPI_TAB_SH + 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 1 a1 a2 a3 a4 a5 a6 a7 0 PPI_TAB PPI_TAB_SH s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT TSH MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  lazymatch type of TSH with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TSH end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. ppi_loop SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w2 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m (PPI_TAB_SH + 2) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_name sp gp tp t0 t1 t2 1 A_FIPS a4 a5 a6 a7 (-16) (PPI_TAB + 16) (PPI_TAB_SH + 2) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 2 a1 a2 a3 a4 a5 a6 a7 (-8) (PPI_TAB + 8) (PPI_TAB_SH + 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT TSH MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  lazymatch type of TSH with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TSH end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. ppi_loop SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w3 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m (PPI_TAB_SH + 3) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_name sp gp tp t0 t1 t2 1 A_OUTPUT a4 a5 a6 a7 (-24) (PPI_TAB + 24) (PPI_TAB_SH + 3) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 3 a1 a2 a3 a4 a5 a6 a7 (-16) (PPI_TAB + 16) (PPI_TAB_SH + 2) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT TSH MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  lazymatch type of TSH with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TSH end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. ppi_loop SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w4 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m (PPI_TAB_SH + 4) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_name sp gp tp t0 t1 t2 1 A_INPUT a4 a5 a6 a7 (-32) (PPI_TAB + 32) (PPI_TAB_SH + 4) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 4 a1 a2 a3 a4 a5 a6 a7 (-24) (PPI_TAB + 24) (PPI_TAB_SH + 3) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT TSH MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  lazymatch type of TSH with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TSH end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. ppi_loop SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w5 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m (PPI_TAB_SH + 5) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_name sp gp tp t0 t1 t2 1 A_STRUCTURE a4 a5 a6 a7 (-40) (PPI_TAB + 40) (PPI_TAB_SH + 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 5 a1 a2 a3 a4 a5 a6 a7 (-32) (PPI_TAB + 32) (PPI_TAB_SH + 4) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT TSH MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  lazymatch type of TSH with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in TSH end.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. ppi_loop SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w6 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_val1 sp gp tp t0 t1 t2 0 A_YES a4 a5 a6 a7 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_name sp gp tp t0 t1 t2 6 a1 a2 a3 a4 a5 a6 a7 (-40) (PPI_TAB + 40) (PPI_TAB_SH + 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. zstep. th_if_lit. do 4 zstep. th_if_lit.
  do 6 zstep.
  ppi_wrap SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w7 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> mem_inv asegs m ->
  evt asegs (ppi_mid_post SITE_ppi_val2 sp gp tp t0 t1 t2 0 A_NO a4 a5 a6 a7 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (ppi_ret SITE_ppi_val1 sp gp tp t0 t1 t2 1 a1 a2 a3 a4 a5 a6 a7 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT MI. unfold ppi_ret, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 80, SP - 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP - 64)]) by ut_fp_lia.
  assert (HWS : sh_fp [(SP - 80, SP - 64)]) by sh_fp_lia.
  ppi_norm. zstep. th_if_lit.
  do 5 zstep.
  ppi_wrap SP ST. ppi_mid_done SP.
Qed.

(* [comment removed for export] *)
Lemma ppi_w8 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z)
    (j : list byte) (s5v s4v s3v s2v s1v s0v rav : word),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -64) (ppi_fr j s5v s4v s3v s2v s1v s0v rav) -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) (Z_to_bv 64 2) a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom asegs)
       /\ stk asegs m lo (bv_unsigned sp))
    (ppi_ret SITE_ppi_val2 sp gp tp t0 t1 t2 2 a1 a2 a3 a4 a5 a6 a7 1 (PPI_TAB + 48) (PPI_TAB_SH + 6) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until rav. intros ST HLO HLOS SPH FR MI. unfold ppi_ret, ppi_fr, SITE_ppi_name, SITE_ppi_val1, SITE_ppi_val2, PPI_TAB_SH, PPI_TAB, PPI_CTX in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  ppi_norm. zstep. zstep. th_if_lit.
  do 8 zstep.
  th_release FR SP.
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. split; [reflexivity| assumption].
Qed.

(* [comment removed for export] *)
Definition zb (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition s_provider : list byte := zb [112; 114; 111; 118; 105; 100; 101; 114].
Definition s_version : list byte := zb [118; 101; 114; 115; 105; 111; 110].
Definition s_fips : list byte := zb [102; 105; 112; 115].
Definition s_output : list byte := zb [111; 117; 116; 112; 117; 116].
Definition s_input : list byte := zb [105; 110; 112; 117; 116].
Definition s_structure : list byte := zb [115; 116; 114; 117; 99; 116; 117; 114; 101].
Definition s_yes : list byte := zb [121; 101; 115].
Definition s_no : list byte := zb [110; 111].
(* [comment removed for export] *)
Definition ppi_lit (A : Z) (str : list byte) (k : nat) : Prop :=
  ro_bytes asegs A (str ++ Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) k) /\ ~ In (Z_to_bv 8 0) str /\ str <> [] /\ Z.of_nat (length str) + 16 <= 64512
  /\ (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (repeat (Z_to_bv 8 0) k))
  /\ 0x10000 <= A /\ A + Z.of_nat (length str) + 1 + Z.of_nat (length (repeat (Z_to_bv 8 0) k)) <= SEGTOP_A.
Ltac ppi_lit_tac := split; [apply ro_bytes_b_sound; vm_compute; reflexivity|];
  split; [vm_compute; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH|];
  split; [cbn; discriminate|]; unfold SEGTOP_A; cbn; lia.
Lemma lit_provider : ppi_lit A_PROVIDER s_provider 7. Proof. unfold ppi_lit, A_PROVIDER, s_provider, zb. ppi_lit_tac. Qed.
Lemma lit_version : ppi_lit A_VERSION s_version 0. Proof. unfold ppi_lit, A_VERSION, s_version, zb. ppi_lit_tac. Qed.
Lemma lit_fips : ppi_lit A_FIPS s_fips 3. Proof. unfold ppi_lit, A_FIPS, s_fips, zb. ppi_lit_tac. Qed.
Lemma lit_output : ppi_lit A_OUTPUT s_output 1. Proof. unfold ppi_lit, A_OUTPUT, s_output, zb. ppi_lit_tac. Qed.
Lemma lit_input : ppi_lit A_INPUT s_input 2. Proof. unfold ppi_lit, A_INPUT, s_input, zb. ppi_lit_tac. Qed.
Lemma lit_structure : ppi_lit A_STRUCTURE s_structure 6. Proof. unfold ppi_lit, A_STRUCTURE, s_structure, zb. ppi_lit_tac. Qed.
Lemma lit_yes : ppi_lit A_YES s_yes 4. Proof. unfold ppi_lit, A_YES, s_yes, zb. ppi_lit_tac. Qed.
Lemma lit_no : ppi_lit A_NO s_no 5. Proof. unfold ppi_lit, A_NO, s_no, zb. ppi_lit_tac. Qed.

Definition H_PROVIDER : Z := 0x672244bb. Definition H_VERSION : Z := 0x64dc8d0b. Definition H_FIPS : Z := 0x6093f86e. Definition H_OUTPUT : Z := 0xdbaceec9.
Definition H_INPUT : Z := 0x5a0038b. Definition H_STRUCTURE : Z := 0x72db842e. Definition H_YES : Z := 0x55e72115. Definition H_NO : Z := 0x255844.
Lemma hash_provider : lh_strhash s_provider = H_PROVIDER. Proof. vm_compute. reflexivity. Qed.
Lemma hash_version : lh_strhash s_version = H_VERSION. Proof. vm_compute. reflexivity. Qed.
Lemma hash_fips : lh_strhash s_fips = H_FIPS. Proof. vm_compute. reflexivity. Qed.
Lemma hash_output : lh_strhash s_output = H_OUTPUT. Proof. vm_compute. reflexivity. Qed.
Lemma hash_input : lh_strhash s_input = H_INPUT. Proof. vm_compute. reflexivity. Qed.
Lemma hash_structure : lh_strhash s_structure = H_STRUCTURE. Proof. vm_compute. reflexivity. Qed.
Lemma hash_yes : lh_strhash s_yes = H_YES. Proof. vm_compute. reflexivity. Qed.
Lemma hash_no : lh_strhash s_no = H_NO. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bk_provider : Z.to_nat (H_PROVIDER mod 8) = 3%nat. Proof. reflexivity. Qed.
Lemma bk_version : Z.to_nat (H_VERSION mod 8) = 3%nat. Proof. reflexivity. Qed.
Lemma bk_fips : Z.to_nat (H_FIPS mod 8) = 6%nat. Proof. reflexivity. Qed.
Lemma bk_output : Z.to_nat (H_OUTPUT mod 8) = 1%nat. Proof. reflexivity. Qed.
Lemma bk_input : Z.to_nat (H_INPUT mod 8) = 3%nat. Proof. reflexivity. Qed.
Lemma bk_structure : Z.to_nat (H_STRUCTURE mod 8) = 6%nat. Proof. reflexivity. Qed.
Lemma bk_yes : Z.to_nat (H_YES mod 8) = 5%nat. Proof. reflexivity. Qed.
Lemma bk_no : Z.to_nat (H_NO mod 8) = 4%nat. Proof. reflexivity. Qed.
Definition nb16 (b1 b3 b4 b5 b6 : list pnode) : list (list pnode) := [[]; b1; []; b3; b4; b5; b6; []; []; []; []; []; []; []; []; []].
Lemma nb16_empty : repeat [] 16 = nb16 [] [] [] [] []. Proof. reflexivity. Qed.
