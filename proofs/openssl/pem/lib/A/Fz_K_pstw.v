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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Th_mutex Fz_T_lock Fz_env Fz_M_malloc Fz_T_sk Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_skw Fz_K_sk Fz_I2_ppis Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Definition e_property_string : Z := 0x20c090.
Definition e_property_name : Z := 0x20c068.
Definition e_property_value : Z := 0x20c6fc.
Definition e_get_data : Z := 0x1f77d0.
Definition e_lh_error : Z := 0x201498.
Definition SITE_ps_smalloc : Z := 0x20c10c.
Definition SITE_ps_getdata : Z := 0x20c1a0.
Definition SITE_ps_rlock : Z := 0x20c1f4.
Definition SITE_ps_retr1 : Z := 0x20c208.
Definition SITE_ps_unlock1 : Z := 0x20c284.
Definition SITE_ps_wlock : Z := 0x20c29c.
Definition SITE_ps_retr2 : Z := 0x20c2e8.
Definition SITE_ps_strlen : Z := 0x20c2f4.
Definition SITE_ps_malloc : Z := 0x20c30c.
Definition SITE_ps_memcpy : Z := 0x20c328.
Definition SITE_ps_push : Z := 0x20c490.
Definition SITE_ps_insert : Z := 0x20c4a8.
Definition SITE_ps_lherr : Z := 0x20c4b0.
Definition SITE_ps_unlock2 : Z := 0x20c220.
Definition PS_FILE : Z := 0x4b980.
Definition PS_MAGIC : Z := 0x41b58ab3.
Definition PS_DESCR : Z := 0x2ba37.
Definition PS_RETIRED : Z := 0x45e0360e.
Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

(* [comment removed for export] *)
Lemma gd3_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo ps : Z),
  a0 = Z_to_bv 64 PPI_CTX -> a1 = Z_to_bv 64 3 ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] -> ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ps) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_get_data) fc None m (seg_rom asegs)).
Proof.
  intros until ps. intros -> -> PSC GSH UT SHC ST LO0 LO HTOP MI. unfold e_get_data, PPI_CTX, CTX_PSD, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 zstep. zstep. do 3 zstep.
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  do 6 zstep. zstep.
  do 3 zstep. zstep. zsh. zstep. th_if_lit.
  zstep. do 4 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma lherr_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh B items : Z),
  a0 = Z_to_bv 64 lh -> rw_cells asegs m lh (plh_cells B items) -> acc asegs m lh 104 -> 0 < lh -> lh mod 8 = 0 -> lh + 104 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a1' a2' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_lh_error) fc None m (seg_rom asegs)).
Proof.
  intros until items. intros -> SC ACC L0 LAL LLO UT SHC ST LO0 LO HTOP MI. unfold e_lh_error, plh_cells, e_property_cmp, e_property_hash, T_HW, T_CW, T_DAW, T_DAAW, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  do 2 zstep. do 4 zstep. zstep. zsh. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 0) by lia. do 2 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition ps_ftail (s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
Definition ps_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (C NM CR S : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 64) a1' a2' (Z_to_bv 64 S) a4 a5 a6 a7 s2 (Z_to_bv 64 C) s4 (Z_to_bv 64 S) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 NM) (Z_to_bv 64 CR) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (C8 (Z_to_bv 64 0) :: CB 48 j :: ps_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma ps_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd C NM CR S : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= C < 2^64 -> 0 <= NM < 2^64 -> 0 <= CR < 2^64 -> 0 <= S < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (ps_w0_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 C NM CR S F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) (Z_to_bv 64 NM) (Z_to_bv 64 CR) (Z_to_bv 64 S) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_property_string) fc None m (seg_rom asegs)).
Proof.
  intros until S. intros HP HPM HC HNM HCR HS ST HLO HLOS SPH UT SHC UAR MI. unfold e_property_string, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP)]) by ut_fp_lia.
  th_frame 160%nat [8; 48; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. do 13 zstep. zstep.
  zstep.
  rewrite (land_m32_pad (SP + -160) pd) by (first [lia | replace (SP + -160) with (SP + (-5) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  do 4 zstep. do 4 zstep. zstep. zstep. zstep.
  zstep. th_if_lit. zstep. zstep.
  destruct (stk_split asegs _ lo (SP + -160 - pd) (SP + -160) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ps_w0_post, SITE_ps_smalloc, e_stack_malloc, ps_ftail. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition psd_cells (pk pl1 pl2 ni vi pq1 pq2 : Z) : list cell :=
  [C8 (Z_to_bv 64 pk); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); C4 (Z_to_bv 64 ni); C4 (Z_to_bv 64 vi); C8 (Z_to_bv 64 pq1); C8 (Z_to_bv 64 pq2)].
(* [comment removed for export] *)
Definition ps_fcells (hj : list byte) (sv : word) (pj tj : list byte) : list cell :=
  [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj; C8 sv; CB 8 pj; CB 8 tj].
Definition ps_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Definition nmz (nm : bool) : Z := if nm then 1 else 0.
Definition t_of (nm : bool) (pl1 pl2 : Z) : Z := if nm then pl1 else pl2.
Definition q_of (nm : bool) (pq1 pq2 : Z) : Z := if nm then pq1 else pq2.
Definition off_idx (nm : bool) : Z := if nm then 24 else 28.

Lemma ps_acc16 : forall (m : mem) f, f mod 64 = 0 -> 0 < f -> rw_cells asegs m (shad f) ps_shadow -> acc asegs m (f + 32) 16.
Proof.
  intros m f F64 F0 FFS. unfold ps_shadow in FFS.
  assert (E32 : shad (f + 32) = shad f + 4) by (rewrite (shad_aligned_add f 32) by lia; reflexivity).
  change 16 with (8 * Z.of_nat 2). apply (acc_zero_run asegs m (f + 32) 2); [clear - F64; Z.div_mod_to_equations; lia| lia|]. rewrite E32. cbn [repeat].
  change (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: ?r) with ([C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ++ r) in FFS.
  pose proof (rw_cells_skip m (shad f) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ FFS) as X.
  apply (proj1 (rw_cells_app m _ _ _)) in X. destruct X as [X _].
  pose proof (proj2 (proj1 X)) as Y. cbn [cells_size csize Nat.add cells_bytes cbytes app] in Y. replace (shad f + Z.of_nat 4) with (shad f + 4) in Y by lia.
  unfold z8. exact Y.
Qed.

(* [comment removed for export] *)
Definition ps_w1a_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f lo pd : Z) (fj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j' hj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 (-15)) (Z_to_bv 64 PS_DESCR) (Z_to_bv 64 e_property_string) a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 0x20c194) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp - 152, bv_unsigned sp - 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j' :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) ps_shadow.

Lemma ps_w1a : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (f lo pd : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 56 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -160) (C8 (Z_to_bv 64 0) :: CB 48 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (shad f) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (ps_w1a_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 F fc rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v f lo pd fj m)
    (MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ps_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FSEG FLO FSH LO HLOS SPH FR GAPS ST FFC FFS MI. unfold SITE_ps_smalloc, ps_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 152, SP - 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (clear - SPH FLO LO HLOS; Z.div_mod_to_equations; lia); lia).
  assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP - 152, SP - 104)]) by (clear - F0 FSEG SHR LO HLOS SPH FLO HP; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1. unfold shad, SHB in FFS.
  apply (rw_cells_split_CB asegs _ f [] 56 fj [] [8; 8; 8; 32]%nat) in FFC; [| reflexivity]; cbn [mk_CB_cells app] in FFC.
  zstep. zstep. zstep.
  zstep. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zstep.
  1: pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB.
  2: pose proof (rw_cells_blur _ _ [_; _; _; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB; clear FR.
  all: do 3 zstep; zstep; rewrite (shr3_div f) by lia; do 3 zstep.
  all: do 3 (zstep; lfix).
  all: zstep; zstep; do 4 (zstep; lfix).
  all: zstep; do 4 (zstep; lfix).
  all: subst SP; unfold ps_w1a_post, SITE_ps_smalloc, ps_ftail, ps_shadow, PS_MAGIC, PS_DESCR, e_property_string.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.
Qed.

(* [comment removed for export] *)
Lemma ps_fsplit : forall (m : mem) f hj,
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj] ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 (firstn 8 hj)]
  /\ rw_cells asegs m (f + 32) [CB 8 (firstn 8 (skipn 8 hj))] /\ rw_cells asegs m (f + 40) [CB 16 (firstn 16 (skipn 8 (skipn 8 hj)))].
Proof.
  intros m f hj FFC.
  change (rw_cells asegs m f ([C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string)] ++ [CB 32 hj])) in FFC.
  apply (rw_cells_split_CB asegs _ f _ 32 hj [] [8; 8; 16]%nat) in FFC; [| reflexivity]; cbn [mk_CB_cells app] in FFC.
  change (rw_cells asegs m f ([C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 (firstn 8 hj)] ++ ([CB 8 (firstn 8 (skipn 8 hj))] ++ [CB 16 (firstn 16 (skipn 8 (skipn 8 hj)))]))) in FFC.
  apply (proj1 (rw_cells_app m _ _ _)) in FFC. destruct FFC as [FFCa FFC]. apply (proj1 (rw_cells_app m _ _ _)) in FFC. destruct FFC as [FFCw FFCb].
  cbn [cells_size csize Nat.add] in FFCw, FFCb. split; [exact FFCa|]. split.
  - lazymatch type of FFCw with rw_cells _ _ ?a _ => replace a with (f + 32) in FFCw by (clear; lia) end. exact FFCw.
  - lazymatch type of FFCb with rw_cells _ _ ?a _ => replace a with (f + 40) in FFCb by (clear; lia) end. exact FFCb.
Qed.

Lemma ps_fjoin : forall (m : mem) f hj1 (sv : word) hj2,
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1] ->
  rw_cells asegs m (f + 32) [C8 sv] -> rw_cells asegs m (f + 40) [CB 16 hj2] ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 sv; CB 16 hj2].
Proof.
  intros m f hj1 sv hj2 A B C.
  change (rw_cells asegs m f ([C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1] ++ ([C8 sv] ++ [CB 16 hj2]))).
  apply (proj2 (rw_cells_app m _ _ _)). split; [exact A|]. apply (proj2 (rw_cells_app m _ _ _)). cbn [cells_size csize Nat.add]. split.
  - lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (f + 32) by (clear; lia) end. exact B.
  - lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (f + 40) by (clear; lia) end. exact C.
Qed.

(* [comment removed for export] *)
Definition ps_w1b_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word)
    (nm : bool) (f lo pd S ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (j' hj1 hj2 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ps_strlen) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0' t1' t2' sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) (Z_to_bv 64 S) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 f) (Z_to_bv 64 ps) (Z_to_bv 64 (Z.shiftr ps 3 + 2147450880)) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 (t_of nm pl1 pl2))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3' t4' t5' t6')
            F (Z_to_bv 64 e_strlen) fc None m' (seg_rom asegs)
    /\ munch [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j' :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 8) [C8 (Z_to_bv 64 (off_idx nm))]
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 16) [C8 (Z_to_bv 64 (nmz nm))]
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 24) [C8 (Z_to_bv 64 (t_of nm pl1 pl2))]
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 hj1; C8 (Z_to_bv 64 S); CB 16 hj2]
    /\ rw_cells asegs m' (f / 8 + 2147450880) ps_shadow
    /\ rw_cells asegs m' CTX_PSD [C8 (Z_to_bv 64 ps)] /\ rw_cells asegs m' ps (psd_cells pk pl1 pl2 ni vi pq1 pq2)
    /\ rw_cells asegs m' pk (mutex_cells z64 (Z_to_bv 64 16)) /\ plh_rep m' (t_of nm pl1 pl2) B items bks.

Lemma ps_w1b : forall (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (nm : bool) (lo pd f S ps pk pl1 pl2 ni vi pq1 pq2 B items : Z) (bks : list (list pnode)) (str : list byte) (j hj : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  (pd = 0 \/ pd = 16) -> (bv_unsigned sp + -160 - pd) mod 32 = 0 ->
  0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 56 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 320 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: ps_ftail s11v s10v s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  acc asegs m (bv_unsigned sp + -160 - pd - 144) 144 ->
  rw_cells asegs m f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 32 hj] ->
  rw_cells asegs m (f / 8 + 2147450880) ps_shadow ->
  rw_cells asegs m CTX_PSD [C8 (Z_to_bv 64 ps)] -> ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m ps (psd_cells pk pl1 pl2 ni vi pq1 pq2) -> acc asegs m ps 48 -> 0 < ps -> ps mod 16 = 0 -> ps + 48 <= lo -> 0x10007fff8000 <= ps -> (ps + 48 <= f \/ f + 64 <= ps) ->
  rw_cells asegs m pk (mutex_cells z64 z64) -> 0 < pk -> pk mod 16 = 0 -> pk + 40 <= lo -> 0x10007fff8000 <= pk -> (pk + 40 <= f \/ f + 64 <= pk) ->
  plh_rep m (t_of nm pl1 pl2) B items bks ->
  acc asegs m (t_of nm pl1 pl2) 104 -> 0 < t_of nm pl1 pl2 -> t_of nm pl1 pl2 + 104 <= lo -> (t_of nm pl1 pl2 + 104 <= f \/ f + 64 <= t_of nm pl1 pl2) ->
  acc asegs m B 128 -> 0 < B -> B + 128 <= lo -> (B + 128 <= f \/ f + 64 <= B) ->
  (forall n, In n (concat bks) -> acc asegs m (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo /\ (fst n + 24 <= f \/ f + 64 <= fst n) /\ (fst n + 24 <= pk \/ pk + 40 <= fst n)) ->
  0 < S -> bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 20 ->
  acc asegs m S (Z.of_nat (length str) + 1) -> S + Z.of_nat (length str) + 1 <= 0xbc6000 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  (ps + 48 <= t_of nm pl1 pl2 \/ t_of nm pl1 pl2 + 104 <= ps) -> (pk + 40 <= t_of nm pl1 pl2 \/ t_of nm pl1 pl2 + 104 <= pk) ->
  (ps + 48 <= pk \/ pk + 40 <= ps) -> (pk + 40 <= B \/ B + 128 <= pk) ->
  mem_inv asegs m ->
  evt asegs (ps_w1b_post sp gp tp F fc rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v nm f lo pd S ps pk pl1 pl2 ni vi pq1 pq2 B items bks m)
    (MS (mkR (Z_to_bv 64 SITE_ps_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 (-15)) (Z_to_bv 64 PS_DESCR) (Z_to_bv 64 e_property_string) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 PPI_CTX) s4 (Z_to_bv 64 S) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (nmz nm)) (Z_to_bv 64 1) s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 0x20c194) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros HP RBAL F0 F64 FSEG FLO FSH LO HLOS SPH UT SHC FR GAPS ST ACCS FFC FFS CELL GSH PSC PSA PS0 PSAL PSLO PSHI PSF LKC PK0 PKAL PKLO PKHI PKF
         REP ACCL L0 LLO LHF ACCB B0 BLO BF NODES S0 STR NONUL NE LEN SACC SIMG HASHES PSLH PKLH PSPK PKB MI.
  unfold SITE_ps_smalloc, g_shadow_memory_dynamic_address, SHB, psd_cells, ps_ftail, PPI_CTX, CTX_PSD in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)]) by (clear - F0 FSEG LO HLOS SPH FLO HP PKHI; ut_fp_lia).
  assert (HWS : sh_fp [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)]) by (clear - F0 FSEG FSH LO HLOS SPH FLO HP PKHI; sh_fp_lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) = bv_unsigned sp + -160 - pd) by (apply unsigned_lit; clear - RSP LO HLOS HP; lia).
  pose proof (div8_facts f) as Q1. unfold mutex_cells in LKC. unfold ps_shadow in FFS.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (clear - SPH FLO LO HLOS; Z.div_mod_to_equations; lia); lia).
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  assert (PSAL8 : ps mod 8 = 0) by (clear - PSAL; Z.div_mod_to_equations; lia). assert (PKAL4 : pk mod 4 = 0) by (clear - PKAL; Z.div_mod_to_equations; lia).
  assert (D8 : (f + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (RB16 : (bv_unsigned sp + -160 - pd) mod 16 = 0) by (clear - RBAL; Z.div_mod_to_equations; lia).
  pose proof (ps_acc16 m f F64 F0 ltac:(unfold shad, SHB, ps_shadow; exact FFS)) as FACC.
  destruct (ps_fsplit m f hj FFC) as (FFCa & FFCw & FFCb). clear FFC.
  (* [comment removed for export] *)
  assert (LATER : forall mx, munch [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)] m mx ->
       acc asegs mx ps 48 /\ acc asegs mx (f + 32) 8 /\ acc asegs mx S (Z.of_nat (length str) + 1) /\ acc asegs mx (t_of nm pl1 pl2) 104 /\ acc asegs mx B 128
    /\ acc asegs mx (bv_unsigned sp + -160 - pd - 144) 144 /\ img_untouched mx /\ plh_rep mx (t_of nm pl1 pl2) B items bks
    /\ (forall n, In n (concat bks) -> acc asegs mx (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo)).
  { intros mx MUx. split; [exact (acc_munch_sh _ m mx _ _ PSA MUx HWS ltac:(lia) ltac:(clear - PSLO LO SPH; lia))|].
    split; [exact (acc_munch_sh _ m mx _ _ (acc_sub asegs m (f + 32) 16 (f + 32) 8 FACC ltac:(lia) ltac:(lia)) MUx HWS ltac:(lia) ltac:(clear - FLO LO SPH; lia))|].
    split; [exact (acc_munch_sh _ m mx _ _ SACC MUx HWS ltac:(lia) ltac:(clear - SIMG; lia))|].
    split; [exact (acc_munch_sh _ m mx _ _ ACCL MUx HWS ltac:(lia) ltac:(clear - LLO LO SPH; lia))|].
    split; [exact (acc_munch_sh _ m mx _ _ ACCB MUx HWS ltac:(lia) ltac:(clear - BLO LO SPH; lia))|].
    split; [exact (acc_munch_sh _ m mx _ _ ACCS MUx HWS ltac:(clear - LO HLOS HP; lia) ltac:(clear - SPH HP; lia))|].
    split; [exact (ut_munch _ m mx UT MUx HWU)|].
    split.
    - apply (plh_rep_munch _ _ _ _ _ _ _ REP MUx). intros a [Ha|[Ha|(n & Hn & Ha)]]; cbn [outside].
      + clear - Ha LHF LLO LO PKLH HP. lia.
      + clear - Ha BF BLO LO PKB HP. lia.
      + destruct (NODES n Hn) as (_ & _ & X3 & X4 & X5). clear - Ha X3 X4 X5 LO HP. lia.
    - intros n Hn. destruct (NODES n Hn) as (X1 & X2 & X3 & X4 & X5). split; [exact (acc_munch_sh _ m mx _ _ X1 MUx HWS ltac:(lia) ltac:(clear - X3 LO SPH; lia))| exact (conj X2 X3)]. }
  (* [comment removed for export] *)
  assert (KEEP : forall mx, munch [(f + 32, f + 40); (bv_unsigned sp - 304 - pd, bv_unsigned sp - 104); (pk + 4, pk + 8)] m mx -> wmono asegs m mx ->
       rw_cells asegs mx ps [C8 (Z_to_bv 64 pk); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); C4 (Z_to_bv 64 ni); C4 (Z_to_bv 64 vi); C8 (Z_to_bv 64 pq1); C8 (Z_to_bv 64 pq2)]
    /\ bytes_at asegs mx S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs mx f [C8 (Z_to_bv 64 PS_MAGIC); C8 (Z_to_bv 64 PS_DESCR); C8 (Z_to_bv 64 e_property_string); CB 8 (firstn 8 hj)]
    /\ rw_cells asegs mx (f + 40) [CB 16 (firstn 16 (skipn 8 (skipn 8 hj)))]
    /\ rw_cells asegs mx (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))]
    /\ rw_cells asegs mx 12187176 [C8 (Z_to_bv 64 ps)] /\ ro_cells asegs mx 2148974277 [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mx 6736696 [C8 (Z_to_bv 64 2147450880)]).
  { intros mx MUx WMx.
    split; [apply (rw_cells_transport asegs _ m mx _ _ PSC MUx WMx); cbn [disjoint_from cells_size csize Nat.add]; clear - PSF PSLO LO HP PSPK; lia|].
    split; [apply (bytes_at_transport asegs _ m mx _ _ STR MUx); cbn [disjoint_from]; rewrite length_app; cbn [length]; clear - SIMG FSEG LO HLOS HP PKHI; lia|].
    split; [apply (rw_cells_transport asegs _ m mx _ _ FFCa MUx WMx); cbn [disjoint_from cells_size csize Nat.add]; clear - FLO LO HP PKF; lia|].
    split; [apply (rw_cells_transport asegs _ m mx _ _ FFCb MUx WMx); cbn [disjoint_from cells_size csize Nat.add]; clear - FLO LO HP PKF; lia|].
    split; [apply (rw_cells_transport asegs _ m mx _ _ FFS MUx WMx); cbn [disjoint_from cells_size csize Nat.add]; clear - SHR FSH FSEG Q1 LO HLOS HP PKHI; lia|].
    split; [apply (rw_cells_transport asegs _ m mx _ _ CELL MUx WMx); cbn [disjoint_from cells_size csize Nat.add]; clear - FSEG LO HLOS HP PKHI; lia|].
    split; [apply (ro_cells_transport asegs _ m mx _ _ GSH MUx); cbn [disjoint_from cells_size csize Nat.add]; clear - FSH FSEG LO HLOS HP PKHI F0; lia|].
    apply (ro_cells_transport asegs _ m mx _ _ SHC MUx); cbn [disjoint_from cells_size csize Nat.add]; clear - FSEG LO HLOS HP PKHI; lia. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (gd3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo ps); try reflexivity; try eassumption.
    all: rewrite ?EU1; first [eassumption| clear - LO HLOS SPH HP RSP; lia]. }
  clear UT SHC FFS CELL GSH PSC PSF REP ACCL LHF ACCB BF NODES STR SACC PSLH PKLH PSPK PKB FSH F64 RBAL PSAL PKAL FACC FFCa FFCb Q1 SHR ACCS.
  cbv beta. intros ms' PO. hnf in PO. rewrite ?EU1 in PO. revert ms' PO.
  lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct nm; cbn [nmz t_of q_of off_idx] in *; (zstep; try th_if_lit; zstep); [zstep|]; destruct HP as [-> | ->].
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) in * by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) in * by lia.
  all: destruct (KEEP _ MU WM) as (PSCx & _).
  all: zstep; zstep; zstep; zstep; zsh; zstep; th_if_lit.
  all: do 3 zstep.
  all: destruct (KEEP _ MU WM) as (PSCx & _).
  all: do 4 zstep.
  all: clear PSCx.
  all: zsh; zstep; first [th_if_lit | ubs_if].
  all: destruct (KEEP _ MU WM) as (PSCx & _).
  all: zstep; zstep.
  all: clear PSCx.
  (* [comment removed for export] *)
  all: eapply evt_cut; [eapply (T_read_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); rewrite ?unsigned_lit, ?EU1 by lia; first [eassumption| lia] |].
  all: cbv beta; intros ms' PO; hnf in PO; repeat (rewrite unsigned_lit in PO by lia); rewrite ?EU1 in PO; unfold mutex_cells in PO; revert ms' PO.
  all: lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  all: zstep; th_if_lit.
  all: zstep; lfix.
  all: zstep; zstep; zstep.
  (* [comment removed for export] *)
  all: destruct (LATER _ MU) as (PSAx & DAx & SAx & LAx & BAx & STAx & UTx & REPx & NODESx); destruct (KEEP _ MU WM) as (_ & STRx & _ & _ & _ & _ & _ & SHCx).
  all: lazymatch type of REPx with plh_rep _ ?lhv _ _ _ =>
         eapply evt_cut; [eapply (plh_retrieve_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lhv B items bks (f + 32) S lo str); rewrite ?EU1; try eassumption; try reflexivity |] end.
  all: try (apply (acc_sub asegs _ _ _ _ _ STAx); lia).
  all: try (clear - D8 RB16 LEN SIMG HLOS LO FLO F0 SPH; lia).
  all: clear PSAx DAx SAx LAx BAx STAx UTx REPx NODESx STRx SHCx.
  all: cbv beta; intros ms' PO; hnf in PO; rewrite ?EU1 in PO; revert ms' PO.
  all: lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  all: zstep; th_if_lit.
  all: zstep; th_if_lit.
  all: zstep; zsh; zstep; th_if_lit.
  all: destruct (KEEP _ MU WM) as (PSCx & _); zstep; zstep; clear PSCx.
  (* [comment removed for export] *)
  all: eapply evt_cut; [eapply (T_unlock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); rewrite ?unsigned_lit, ?EU1 by lia; first [eassumption| lia] |].
  all: cbv beta; intros ms' PO; hnf in PO; repeat (rewrite unsigned_lit in PO by lia); rewrite ?EU1 in PO; unfold mutex_cells in PO; revert ms' PO.
  all: lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  all: zstep; zsh; zstep; zstep; zstep; th_if_lit.
  all: destruct (KEEP _ MU WM) as (PSCx & _); zstep; zstep; clear PSCx.
  (* [comment removed for export] *)
  all: eapply evt_cut; [eapply (T_write_lock_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); rewrite ?unsigned_lit, ?EU1 by lia; first [eassumption| lia] |].
  all: cbv beta; intros ms' PO; hnf in PO; repeat (rewrite unsigned_lit in PO by lia); rewrite ?EU1 in PO; unfold mutex_cells in PO; revert ms' PO.
  all: lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  all: zstep; th_if_lit.
  all: zstep; try th_if_lit; zstep.
  all: try lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x20c2a8) _ _ _ _) => zstep end.
  (* [comment removed for export] *)
  all: try (lazymatch goal with G : stk asegs _ (bv_unsigned ?spv + -176) (bv_unsigned ?spv' + -160) |- _ =>
         destruct (stk_carve asegs _ (bv_unsigned sp + -176) (bv_unsigned sp + -160) 16 G ltac:(lia)) as [GAP' [gj GFR]]; clear G;
         change (Z.of_nat 16) with 16 in GAP', GFR; replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) in GAP', GFR by lia end).
  all: zstep; lfix.
  all: try (lazymatch goal with G : rw_cells asegs _ (bv_unsigned ?spv + -176) [CB 8 _; C8 _] |- _ =>
         pose proof (stk_of_rw_cells asegs _ _ _ G) as GAPS; cbn [cells_size csize Nat.add] in GAPS; replace (bv_unsigned sp + -176 + Z.of_nat 16) with (bv_unsigned sp + -160) in GAPS by lia end).
  all: zstep; zstep; zstep.
  (* [comment removed for export] *)
  all: destruct (LATER _ MU) as (PSAx & DAx & SAx & LAx & BAx & STAx & UTx & REPx & NODESx); destruct (KEEP _ MU WM) as (_ & STRx & _ & _ & _ & _ & _ & SHCx).
  all: lazymatch type of REPx with plh_rep _ ?lhv _ _ _ =>
         eapply evt_cut; [eapply (plh_retrieve_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lhv B items bks (f + 32) S lo str); rewrite ?EU1; try eassumption; try reflexivity |] end.
  all: try (apply (acc_sub asegs _ _ _ _ _ STAx); lia).
  all: try (clear - D8 RB16 LEN SIMG HLOS LO FLO F0 SPH; lia).
  all: clear PSAx DAx SAx LAx BAx STAx UTx REPx NODESx STRx SHCx.
  all: cbv beta; intros ms' PO; hnf in PO; rewrite ?EU1 in PO; revert ms' PO.
  all: lazymatch type of MU with munch _ _ ?mc => post_call asegs mc end.
  all: zstep; th_if_lit.
  all: zstep; zstep.
  (* [comment removed for export] *)
  all: try (lazymatch goal with FRh : rw_cells asegs ?mx (bv_unsigned ?spv + -160) (CB 8 ?a :: C8 ?o :: C8 ?n :: C8 ?t :: CB 24 ?b :: ?tl) |- _ =>
         pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 8 a] _ FRh)) as OFFC;
         pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 8 a; C8 o] _ FRh)) as NMC;
         pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 8 a; C8 o; C8 n] _ FRh)) as TC;
         cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OFFC, NMC, TC;
         pose proof (rw_cells_blur _ _ [_; _; _; _; _] _ FRh) as FRB; cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB; clear FRh end).
  all: try (lazymatch goal with FRh : rw_cells asegs ?mx (bv_unsigned ?spv + -160) (C8 ?n :: C8 ?t :: CB 40 ?b :: ?tl), GFRh : rw_cells asegs _ (bv_unsigned _ + -176) [CB 8 ?g; C8 ?o] |- _ =>
         pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 8 g] _ GFRh)) as OFFC;
         pose proof (rw_cells_head _ _ _ _ FRh) as NMC;
         pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [C8 n] _ FRh)) as TC;
         cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OFFC, NMC, TC;
         pose proof (rw_cells_blur _ _ [_; _; _] _ FRh) as FRB; cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB; clear FRh GFRh end).
  all: destruct (LATER _ MU) as (_ & _ & _ & _ & _ & _ & _ & REPx & _); destruct (KEEP _ MU WM) as (PSCx & _ & FFCax & FFCbx & FFSx & CELLx & _).
  all: lazymatch goal with FW : rw_cells asegs ?mx (?fv + 32) [C8 _] |- _ => pose proof (ps_fjoin mx fv _ _ _ FFCax FW FFCbx) as FFCx end.
  all: apply evt_done; unfold ps_w1b_post, SITE_ps_strlen, ps_ftail, ps_shadow, psd_cells, mutex_cells, CTX_PSD; cbn [nmz t_of off_idx].
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: do 18 eexists; split; [reflexivity|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [assumption|].
  all: split; [exact FRB|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [lazymatch goal with |- rw_cells _ _ ?b _ => lazymatch type of OFFC with rw_cells _ _ ?a _ => replace b with a by lia; exact OFFC end end|].
  all: split; [lazymatch goal with |- rw_cells _ _ ?b _ => lazymatch type of NMC with rw_cells _ _ ?a _ => replace b with a by lia; exact NMC end end|].
  all: split; [lazymatch goal with |- rw_cells _ _ ?b _ => lazymatch type of TC with rw_cells _ _ ?a _ => replace b with a by lia; exact TC end end|].
  all: split; [exact FFCx|]. all: split; [exact FFSx|]. all: split; [exact CELLx|]. all: split; [exact PSCx|]. all: split; [eassumption| exact REPx].
Qed.
