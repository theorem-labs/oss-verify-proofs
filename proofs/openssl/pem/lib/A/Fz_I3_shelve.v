(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_W5_icb Th_errno Th_tsd Th_key Th_once Fz_T_once Fz_T_local Fz_T_master1 Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_slx Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation ERRNO_A := (0xba3e4c)%Z (only parsing).
Notation MK_ONCE := (0xb9f500)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation MK_INIT := (0xb9f540)%Z (only parsing).
Notation MK_CLEAN := (0x1f69dc)%Z (only parsing).
Definition e_shelve : Z := 0x1ff254.
Definition SITE_shv_icb : Z := 0x1ff2b4.
Definition SITE_shv_slx : Z := 0x1ff2e8.
Definition e_errno_location : Z := 0x51ad50.

(* [comment removed for export] *)
Lemma shv_w0 : forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo res : Z) (e : word),
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m ERRNO_A [C4 e] -> acc asegs m 0xba3e48 8 ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_shv_icb) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 OPT_BASE_ONLY) z64 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 res) (Z_to_bv 64 (Z.shiftr ERRNO_A 3 + SHB)) (sx32 e) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_shelve) fc None m (seg_rom asegs)).
Proof.
  intros until e. intros UT SHC ERC ERA ST LO0 LO HTOP MI. unfold e_shelve, g_shadow_memory_dynamic_address, SHB, SITE_shv_icb, OPT_BASE_ONLY, e_init_crypto in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EAL : 0xba3e48 mod 8 = 0) by reflexivity.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 zstep. do 3 zstep. zstep. zstep.
  pose proof errno_location_proof as EL. unfold errno_location_stmt in EL.
  eapply evt_cut; [apply EL; rewrite unsigned_lit by lia; lia|]. intros ms' ->. cbv delta [mkR]. th_ret_lit.
  rewrite (unsigned_lit 0xba3ef0) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (acc_granule0_ro mX 12205640 8 12205640 (acc_munch_sh _ m mX _ _ ERA MU HWS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as SH0 end.
  unfold shad, SHB in SH0. replace (12205640 / 8 + 2147450880) with 2148976585 in SH0 by reflexivity. change z8 with (Z_to_bv 8 0) in SH0.
  zstep.          (* [comment removed for export] *)
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep. do 2 zstep. zstep.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption | assumption].
Qed.

(* [comment removed for export] *)
Lemma shv_w1 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ev : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo res nk j : Z) (sh kold w oldcb canary : word) (ib : byte) (old jk : list byte) (rav s0v s1v s2v s3v s4v s5v : word),
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ssp_cells m canary -> rw_cells asegs m (TP_A + -96) [C8 oldcb] -> ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
  SEGTOP_A <= res -> res mod 8 = 0 -> res + 8 <= lo -> (res + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= res) -> rw_cells asegs m res [CB 8 old] -> acc asegs m res 8 ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 368 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t0' t1' a3' a4' a5' a6' a7' : word) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_shv_slx) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) a3' a4' a5' a6' a7'
                    (Z_to_bv 64 res) (Z_to_bv 64 2148976585) ev (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_slx) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 368, bv_unsigned sp - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                 (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] /\ stk asegs m' lo (bv_unsigned sp + -64) /\ ssp_cells m' canary
       /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)]
       /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
       /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
       /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 z64] /\ rw_cells asegs m' res [C8 z64])
    (MS (mkR (Z_to_bv 64 SITE_shv_icb) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 res) (Z_to_bv 64 (Z.shiftr ERRNO_A 3 + SHB)) ev (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_shv_icb) fc None m (seg_rom asegs)).
Proof.
  intros until s5v. intros OC IC KC KSB UT SHC SSP CBC TC NK HNK KL KJ PROBE CASE SLOT RLO RAL RHI RSH RES ACCR FR ST LO0 LO HTOP MI.
  unfold SITE_shv_icb, SITE_shv_slx, e_slx, g_shadow_memory_dynamic_address, SHB in *. unfold SEGTOP_A in RLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                           (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. th_if_lit. do 2 zstep. zstep.
  pose proof T_get_local_ex_first_proof as GLF. unfold T_get_local_ex_first_stmt, ssp_cells, got_ssp, ssp_guard in GLF. unfold ssp_cells, got_ssp, ssp_guard in SSP.
  tcall (GLF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3 nk j 4 sh kold w oldcb canary ib);
    [first [eassumption | exact (proj1 SLOT) | reflexivity | lia | right; reflexivity | exact (ut_munch _ m _ UT MU HWU) | split; eassumption] .. |].
  clear GLF. cbv beta delta [mkR].
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep. fix_lit_store.
  do 3 zstep. zstep.
  finish. all: try eassumption.
  all: lazymatch goal with |- ssp_cells ?mc _ => split;
        [ apply (rw_cells_agree asegs m mc _ _ (proj1 SSP)) | apply (rw_cells_agree asegs m mc _ _ (proj2 SSP)) ];
        [ | exact WM | | exact WM ]; intros y Hy; apply MU; cbv beta in Hy; cbn [outside cells_size csize Nat.add] in *; unfold USTACK_TOP in *; repeat split; try exact I; lia end.
Qed.

(* [comment removed for export] *)
Lemma shv_w2 : forall (sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ev e : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo res : Z) (jk : list byte) (rav s0v s1v s2v s3v s4v s5v : word),
  ev = sx32 e -> rw_cells asegs m ERRNO_A [C4 e] -> acc asegs m 0xba3e48 8 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
       ms = MS (mkR rav sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(ERRNO_A, ERRNO_A + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' ERRNO_A [C4 (sx32 e)])
    (MS (mkR (Z_to_bv 64 SITE_shv_slx) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 res) (Z_to_bv 64 2148976585) ev (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_shv_slx) fc None m (seg_rom asegs)).
Proof.
  intros until s5v. intros -> ERC ERA UT SHC FR ST LO0 LO HTOP MI. unfold SITE_shv_slx, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(ERRNO_A, ERRNO_A + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  pose proof (acc_granule0_ro m 12205640 8 12205640 ERA ltac:(lia) ltac:(lia) eq_refl ltac:(lia)) as SH0.
  unfold shad, SHB in SH0. replace (12205640 / 8 + 2147450880) with 2148976585 in SH0 by reflexivity. change z8 with (Z_to_bv 8 0) in SH0.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. th_if_lit. zstep. zstep. th_if_lit.
  zstep. zstep. do 7 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

Definition e_unshelve : Z := 0x1ff350.
(* [comment removed for export] *)
Definition unshelve_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (lo k MK SA P : Z) (pad top ne oldv : word) (j1 j2 j3 : list byte),
    a0 = z64 -> tp = Z_to_bv 64 TP_A ->
    ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
    ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> ro_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] ->
    0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 -> rw_cells asegs m MK [CB 24 j1; C8 (Z_to_bv 64 SA); CB 40 j2] ->
    0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 -> rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) ->
    0x10007fff8000 <= P -> P mod 8 = 0 -> P + 128 <= lo -> acc asegs m P 128 -> rw_cells asegs m P [C8 oldv; CB 120 j3] -> (SA + 32 <= P \/ P + 128 <= SA) ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' a3' top' : word) (m' : mem),
         ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta z64 oldv)) (Z_to_bv 64 P))
      /\ rw_cells asegs m' P [C8 z64; CB 120 j3])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_unshelve) fc None m (seg_rom asegs)).

Theorem unshelve_proof : unshelve_stmt.
Proof.
  unfold unshelve_stmt, e_unshelve, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until j3.
  intros -> -> OC KC HK KSB UT SHC TSD SLOT MKHI MKAL MKLO ACCM MKC SAHI SAAL SALO ACCS SAC PHI PAL PLO ACCP PC DISJ ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (MK3 : ro_cells asegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)]).
  { pose proof (rw_cells_skip m MK [CB 24 j1] [C8 (Z_to_bv 64 SA); CB 40 j2] MKC) as X. cbn [cells_size csize Nat.add] in X. replace (MK + 8 * 3) with (MK + 24) by lia.
    change [C8 (Z_to_bv 64 SA); CB 40 j2] with ([C8 (Z_to_bv 64 SA)] ++ [CB 40 j2]) in X. exact (proj1 (proj1 (proj1 (rw_cells_app _ _ _ _) X))). }
  pose proof PC as PC'. change [C8 oldv; CB 120 j3] with ([C8 oldv] ++ [CB 120 j3]) in PC'. apply (proj1 (rw_cells_app _ _ _ _)) in PC'. destruct PC' as [PC0 PCR]. cbn [cells_size csize Nat.add] in PCR.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep. zstep. zstep. th_if_lit.
  do 3 zstep. do 2 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  eapply evt_mono.
  { eapply (T_set_local_ex_steady_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 3 MK SA P 4 pad top ne oldv);
      first [reflexivity | eassumption | lia | right; reflexivity
            | exact (acc_munch_sh _ m _ _ _ ACCM MU HWS ltac:(lia) ltac:(lia)) | exact (acc_munch_sh _ m _ _ _ ACCS MU HWS ltac:(lia) ltac:(lia))
            | exact (acc_munch_sh _ m _ _ _ ACCP MU HWS ltac:(lia) ltac:(lia)) | exact (ut_munch _ m _ UT MU HWU) ]. }
  intros ms' (t1' & a1' & a2' & a3' & top' & m' & -> & MU' & WM' & MI' & HT' & ST' & SAC' & PC1'). cbv delta [mkR].
  exists t1', a1', a2', a3', top', m'. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']]; intros xx Hxx; cbn [outside] in *; lia|].
  split; [exact (wmono_trans _ _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact HT'|]. split; [exact ST'|]. split; [exact SAC'|].
  change [C8 (Z_to_bv 64 0); CB 120 j3] with ([C8 (Z_to_bv 64 0)] ++ [CB 120 j3]). apply (proj2 (rw_cells_app _ _ _ _)). split; [exact PC1'|]. cbn [cells_size csize Nat.add].
  lazymatch type of PCR with rw_cells _ ?mm _ _ =>
    apply (rw_cells_agree asegs mm m' _ _ PCR); [intros y Hy; cbv beta in Hy; cbn [cells_size csize Nat.add] in Hy; apply MU'; cbn [outside]; repeat split; try exact I; lia | exact WM'] end.
Qed.

(* [comment removed for export] *)
Lemma shad_slot_in_frame0 : forall fr0 res lo x, fr0 mod 64 = 0 -> res mod 8 = 0 -> fr0 <= res -> res + 8 <= fr0 + 56 -> 0 <= res -> res + 8 <= lo ->
  res + 8 <= 2^47 -> 0x10007fff8000 <= lo -> shad res <= x <= shad (res + 8 - 1) -> shad fr0 <= x < shad (fr0 + 64) /\ x < lo.
Proof.
  intros fr0 res lo x A1 A2 A3 A4 A5 A6 A8 A9 Hx. unfold shad, SHB in *.
  assert (E1 : res = 8 * (res / 8)) by (pose proof (Z.div_mod res 8); lia).
  assert (E2 : fr0 = 64 * (fr0 / 64)) by (pose proof (Z.div_mod fr0 64); lia).
  set (q := res / 8) in *. set (g := fr0 / 64) in *.
  replace ((res + 8 - 1) / 8) with q in Hx by (rewrite E1; replace (8 * q + 8 - 1) with (7 + q * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  replace ((fr0 + 64) / 8) with (8 * g + 8) by (rewrite E2; replace (64 * g + 64) with ((8 * g + 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace (fr0 / 8) with (8 * g) by (rewrite E2; replace (64 * g) with ((8 * g) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  lia.
Qed.

Section CShv.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ICB : init_crypto_base_stmt RT.
Hypothesis C_SLX : slx_first_stmt RT.
Hypothesis GO_mkey : GOBJ MK_KEY 4.
Hypothesis ERRNO_ACC : forall Σ m, ART RT Σ m -> acc asegs m 0xba3e48 8.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition SHV_SITES : list (Z * Z) := (SITE_shv_slx, e_shelve) :: SLX_SITES.
Definition SHV_CALLS : list (Z * Z) := (SITE_shv_slx, e_slx) :: (SITE_shv_slx, e_sa_set) :: SLX_CALLS.
Definition SHV_W (j res : Z) : list (Z * Z) :=
  [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (ERRNO_A, ERRNO_A + 4); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1); (NEXT_KEY, NEXT_KEY + 12);
   (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (TSD_MAIN + 8 * j, TSD_MAIN + 8 * j + 8); (TP_A + -150, TP_A + -149); (res, res + 8)].

(* [comment removed for export] *)
Definition shelve_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (res fr0 nk j : Z) (e od sh kold w oldcb : word) (ib u : byte) (old : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 res -> In (fr0, 0%nat) (rt_frames RT Σ) -> fr0 <= res -> res + 8 <= fr0 + 56 -> res mod 8 = 0 -> rw_cells asegs m res [CB 8 old] -> acc asegs m res 8 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x1d0 <= bv_unsigned sp ->      (* [comment removed for export] *)
  cg_ctx (rt_cg RT Σ) e_shelve (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SHV_SITES SHV_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 < LIVE_MAX -> 1 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m ERRNO_A [C4 e] ->
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] -> ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> 1 <= j ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_shelve m)))
    (fun c => exists (Σ' : rts RT) (MK SA P : Z) (u' : byte) (e' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SHV_W j res) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' ERRNO_A [C4 e']
           /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' res [C8 z64]
           /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
           /\ rw_cells asegs m' P [C8 (Z_to_bv 64 (-1)); CB 120 (zeros 120)]) c
       /\ rt_live RT Σ' = (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP).

Theorem shelve_first_cps : shelve_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary res fr0 nk j e od sh kold w oldcb ib u old
    FDO MST -> -> FRIN FRLO FRHI RAL RES ACC0 ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE STP OD ONCE BRET ERC OC IC KC NK HNK KL KJ PROBE CASE HJ1 SLOT UC CBC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 448 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  destruct (af_frames_range RT AF Σ m fr0 0%nat ART0 FRIN) as (FR0P & FRTOP & FRIMG & FRLV). change (fs_size 0) with 64 in FRTOP, FRIMG, FRLV.
  pose proof (proj2 (af_frames_align RT AF Σ m fr0 0%nat ART0 FRIN)) as FRSEG. pose proof (af_frames_hi RT AF Σ m fr0 0%nat ART0 FRIN) as FRSH. change (fs_size 0) with 64 in FRSH.
  assert (RNUM : SEGTOP_A <= res /\ res + 8 <= lo /\ (res + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= res) /\ res + 8 <= usp - 448 /\ 0 <= res) by (unfold SEGTOP_A in *; lia).
  unfold SEGTOP_A in RNUM.
  assert (SPH0 : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  pose proof (fun x => shad_slot_in_frame0 fr0 res lo x (proj1 (af_frames_align RT AF Σ m fr0 0%nat ART0 FRIN)) RAL FRLO FRHI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RSHAD.
  assert (RCL : forall lv fr sp', In (fr0, 0%nat) fr -> forall x, res <= x < res + 8 -> aclient lv fr sp' x)
    by (intros lv fr sp' Hin x Hx; right; right; right; left; exists fr0, 0%nat; split; [exact Hin| change (fs_size 0) with 64; lia]).
  assert (RCLS : forall lv fr sp', In (fr0, 0%nat) fr -> forall x, shad res <= x <= shad (res + 8 - 1) -> aclient lv fr sp' x)
    by (intros lv fr sp' Hin x Hx; right; right; right; right; exists fr0, 0%nat; split; [exact Hin| change (fs_size 0) with 64; exact (proj1 (RSHAD x Hx))]).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 368) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (shv_w0 ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo res e UT SHC ERC (ERRNO_ACC Σ m ART0) ST HLOS ltac:(lia) SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (jk & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 64) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> rw_cells asegs m1 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m m1 _ _ X); [| exact WM1]. apply BELOW1. intros; lia. }
  pose proof (STAT1 _ _ STP ltac:(cbn; unfold G_IC_STOPPED; lia)) as STP1. pose proof (STAT1 _ _ OD ltac:(cbn; unfold G_IC_OPTSDONE; lia)) as OD1.
  pose proof (STAT1 _ _ ONCE ltac:(cbn; unfold G_IC_BASE_ONCE; lia)) as ONCE1. pose proof (STAT1 _ _ BRET ltac:(cbn; unfold G_IC_BASE_RET; lia)) as BRET1.
  pose proof (STAT1 _ _ ERC ltac:(cbn; lia)) as ERC1. pose proof (STAT1 _ _ OC ltac:(cbn; lia)) as OC1. pose proof (STAT1 _ _ IC ltac:(cbn; lia)) as IC1. pose proof (STAT1 _ _ KC ltac:(cbn; lia)) as KC1.
  pose proof (STAT1 _ _ NK ltac:(cbn; lia)) as NK1. pose proof (STAT1 _ _ KL ltac:(cbn; lia)) as KL1. pose proof (STAT1 _ _ KJ ltac:(cbn; lia)) as KJ1.
  pose proof (STAT1 _ _ SLOT ltac:(cbn; lia)) as SLOT1. pose proof (STAT1 _ _ UC ltac:(cbn; lia)) as UC1. pose proof (STAT1 _ _ CBC ltac:(cbn; lia)) as CBC1.
  assert (PROBE1 : ro_cells asegs m1 (KEYS + 8 * nk) [C8 w]) by (apply (ro_cells_agree asegs m m1 _ _ PROBE); apply BELOW1; cbn [cells_size csize Nat.add]; intros; lia).
  assert (RES1 : rw_cells asegs m1 res [CB 8 old]) by (apply (rw_cells_agree asegs m m1 _ _ RES); [apply BELOW1; cbn [cells_size csize Nat.add]; intros; lia | exact WM1]).
  assert (ACC1 : acc asegs m1 res 8) by (apply (acc_agree m m1 res 8 ACC0 ltac:(lia)); apply BELOW1; intros x Hx; pose proof (proj2 (RSHAD x Hx)); lia).
  (* [comment removed for export] *)
  apply (C_ICB Σ PMc (Z_to_bv 64 SITE_shv_icb) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 res) (Z_to_bv 64 (Z.shiftr ERRNO_A 3 + SHB)) (sx32 e) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { exact Hfr. } { lia. } { exact STP1. } { exact OD1. } { exact ONCE1. } { exact BRET1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  assert (FRIN1 : In (fr0, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; exact FRIN).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & STP2 & OD2 & ONCE2 & BRET2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_shv_icb) in Hc2' by (unfold SITE_shv_icb; lia).
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 x) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. exact (HP _ Ha). }
  assert (STAT2 : forall a cs, rw_cells asegs m1 a cs ->
            (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) ->
            rw_cells asegs m2 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m1 m2 _ _ X); [| exact WM2]. apply AG2. intros x Hx. right; left; apply client_static_intro; lia. }
  pose proof (STAT2 _ _ ERC1 ltac:(cbn; lia)) as ERC2. pose proof (STAT2 _ _ OC1 ltac:(cbn; lia)) as OC2. pose proof (STAT2 _ _ IC1 ltac:(cbn; lia)) as IC2. pose proof (STAT2 _ _ KC1 ltac:(cbn; lia)) as KC2.
  pose proof (STAT2 _ _ NK1 ltac:(cbn; lia)) as NK2. pose proof (STAT2 _ _ KL1 ltac:(cbn; lia)) as KL2. pose proof (STAT2 _ _ KJ1 ltac:(cbn; lia)) as KJ2.
  pose proof (STAT2 _ _ SLOT1 ltac:(cbn; lia)) as SLOT2. pose proof (STAT2 _ _ UC1 ltac:(cbn; lia)) as UC2. pose proof (STAT2 _ _ CBC1 ltac:(cbn; lia)) as CBC2.
  assert (PROBE2 : ro_cells asegs m2 (KEYS + 8 * nk) [C8 w]) by (apply (ro_cells_agree asegs m1 m2 _ _ PROBE1); apply AG2; cbn [cells_size csize Nat.add]; intros x Hx; right; left; apply client_static_intro; lia).
  eassert (FR2 : rw_cells asegs m2 usp1 _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. left; unfold usp1, USTACK_TOP in *; lia. }
  assert (RES2 : rw_cells asegs m2 res [CB 8 old]).
  { apply (rw_cells_agree asegs m1 m2 _ _ RES1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. exact (RCL _ _ usp1 FRIN x ltac:(lia)). }
  assert (ACC2 : acc asegs m2 res 8) by (apply (acc_agree m1 m2 res 8 ACC1 ltac:(lia)); apply AG2; intros x Hx; exact (RCLS _ _ usp1 FRIN x Hx)).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 _ _ MK_KEY ART2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as KSB2. cbn [Z.ltb Z.sub Z.add Z.leb] in KSB2.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG01) as UWCm1.
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWCm1 ltac:(apply AG2; intros x Hx; cbv beta in Hx; left; unfold usp1; lia)) as UWCm2.
  (* [comment removed for export] *)
  pose proof (shv_w1 sp gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (sx32 e) F2 fc2 m2 lo res nk j sh kold w oldcb canary ib old jk ra s0 s1 s2 s3 s4 s5
                OC2 IC2 KC2 KSB2 UT2 SHC2 (cl_env_ssp m2 _ canary UT2 ltac:(exact (cl_env_pres _ _ _ m1 m2 lb canary CLE1 PRES2))) CBC2 (proj1 (TSD Σ1 m2 ART2)) NK2 HNK KL2 KJ2 PROBE2 CASE SLOT2
                ltac:(lia) RAL ltac:(lia) ltac:(lia) RES2 ACC2 FR2 ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & e3 & e4 & e5 & e6 & e7 & m3 & -> & MU3 & WM3 & MI3 & FR3 & ST3 & SSP3 & OC3 & IC3 & KC3 & CBC3 & NK3 & KL3 & KJ3 & SLOT3 & RES3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, FR3. fold usp1 in ST3, FR3.
  assert (MU3' : munch ([(MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] ++ [(usp - 368, usp)]) m2 m3)
    by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 368) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx.
    1: left; unfold USTACK_TOP in *; lia.
    1-6: right; left; apply client_static_intro; lia.
    all: apply (RCL _ _ _ FRIN1); lia. }
  assert (AG23 : agree_on (fun x => usp <= x < USTACK_TOP /\ ~ (res <= x < res + 8)) m2 m3) by (intros a Ha; apply MU3; cbn [outside]; cbv beta in Ha; unfold USTACK_TOP in *; repeat split; try exact I; lia).
  pose proof (cl_env_pres _ _ _ m1 m2 lb canary CLE1 PRES2) as CLE2. pose proof (cl_env_seg _ m2 m3 _ canary CLE2 MU3 ltac:(cl_fp_lia)) as CLE3.
  assert (OFF3 : forall P : Z -> Prop, (forall x, P x -> x < 0xba3e88 /\ (x + 4 <= MK_ONCE \/ MK_INIT + 1 <= x)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (X1 & X2). unfold usp in *. repeat split; try exact I; lia. }
  pose proof (rw_cells_agree asegs m2 m3 _ _ STP2 ltac:(apply OFF3; cbn [cells_size csize Nat.add]; unfold G_IC_STOPPED; intros; lia) WM3) as STP3.
  pose proof (rw_cells_agree asegs m2 m3 _ _ OD2 ltac:(apply OFF3; cbn [cells_size csize Nat.add]; unfold G_IC_OPTSDONE; intros; lia) WM3) as OD3.
  pose proof (rw_cells_agree asegs m2 m3 _ _ ONCE2 ltac:(apply OFF3; cbn [cells_size csize Nat.add]; unfold G_IC_BASE_ONCE; intros; lia) WM3) as ONCE3.
  pose proof (rw_cells_agree asegs m2 m3 _ _ BRET2 ltac:(apply OFF3; cbn [cells_size csize Nat.add]; unfold G_IC_BASE_RET; intros; lia) WM3) as BRET3.
  pose proof (rw_cells_agree asegs m2 m3 _ _ ERC2 ltac:(apply OFF3; cbn [cells_size csize Nat.add]; intros; lia) WM3) as ERC3.
  assert (UC3 : rw_cells asegs m3 (TP_A + -150) [C1 u]) by (apply (rw_cells_agree asegs m2 m3 _ _ UC2); [apply OFF3; cbn [cells_size csize Nat.add]; intros; lia | exact WM3]).
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m3 usp1 [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR3). }
  rewrite <- CG1 in CGH, CTX.
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWCm2 ltac:(intros a Ha; cbv beta in Ha; apply MU3; cbn [outside]; unfold usp, USTACK_TOP in *; repeat split; try exact I; lia)) as UWCm3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_shelve e_slx SITE_shv_slx m3 m3 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWCm3 ltac:(intros a _; reflexivity) FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  (* [comment removed for export] *)
  apply (C_SLX Σ1 PMc (Z_to_bv 64 SITE_shv_slx) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) v0 v1 u2 sp (Z_to_bv 64 ERRNO_A) (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) e3 e4 e5 e6 e7
           (Z_to_bv 64 res) (Z_to_bv 64 2148976585) (sx32 e) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 lo (bv_unsigned ra :: outer) lb canary j u
           FDO MST eq_refl eq_refl eq_refl ltac:(rewrite unsigned_lit_wrap; vm_compute; discriminate) ART3 MI3).
  { fold usp in SPA. assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW). cl_call_ok EU1 ST3 LOW1 SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_shv_slx) by (unfold SITE_shv_slx; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_shv_slx) by (unfold SITE_shv_slx; lia). apply (proj2 CGH). right; left; reflexivity. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV1. lia. } { rewrite CR1. lia. } { exact CLE3. }
  { exact OC3. } { exact KC3. } { lia. } { exact SLOT3. } { exact UC3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & MK & SA & P & u' & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2 & MK0 & MK16 & MKU & SA0 & SA16 & SAU & P0 & P16 & PU).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & SLOT4 & UC4 & MKC4 & SAC4 & PC4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_shv_slx) in Hc4' by (unfold SITE_shv_slx; lia).
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ outside (SLX_W j) x) -> agree_on P m3 m4).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as (X1 & X2). exact (PRES4 a X1 X2). }
  assert (STAT4 : forall a cs, rw_cells asegs m3 a cs -> 0xb8f190 <= a -> a + Z.of_nat (cells_size cs) <= 0xba3e50 -> (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a) -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2 H3. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG4. intros x Hx. split; [right; left; apply client_static_intro; lia|].
    unfold SLX_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (STAT4 _ _ STP3 ltac:(unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia)) as STP4.
  pose proof (STAT4 _ _ OD3 ltac:(unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia)) as OD4.
  pose proof (STAT4 _ _ ONCE3 ltac:(unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia)) as ONCE4.
  pose proof (STAT4 _ _ BRET3 ltac:(unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia)) as BRET4.
  pose proof (STAT4 _ _ ERC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as ERC4. pose proof (STAT4 _ _ OC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as OC4.
  pose proof (STAT4 _ _ IC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as IC4. pose proof (STAT4 _ _ KC3 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as KC4.
  assert (STATK4 : forall a cs, rw_cells asegs m3 a cs -> 0xbc41b8 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc5298 -> rw_cells asegs m4 a cs).
  { intros a cs X H1 H2. apply (rw_cells_agree asegs m3 m4 _ _ X); [| exact WM4]. apply AG4. intros x Hx. split; [right; left; apply client_static_intro; lia|].
    unfold SLX_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  pose proof (STATK4 _ _ NK3 ltac:(lia) ltac:(cbn; lia)) as NK4. pose proof (STATK4 _ _ KL3 ltac:(lia) ltac:(cbn; lia)) as KL4. pose proof (STATK4 _ _ KJ3 ltac:(lia) ltac:(cbn; lia)) as KJ4.
  assert (CBC4 : rw_cells asegs m4 (TP_A + -96) [C8 oldcb]).
  { apply (rw_cells_agree asegs m3 m4 _ _ CBC3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [right; left; apply client_static_intro; lia|].
    unfold SLX_W, G_ALLOW_CUST. cbn [outside]. repeat split; try exact I; lia. }
  eassert (FR4 : rw_cells asegs m4 usp1 _).
  { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|].
    unfold SLX_W, G_ALLOW_CUST. cbn [outside]. unfold usp1, RT_STACK in *. repeat split; try exact I; lia. }
  assert (RES4 : rw_cells asegs m4 res [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m3 m4 _ _ RES3); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [exact (RCL _ _ usp1 FRIN1 x ltac:(lia))|].
    unfold SLX_W, G_ALLOW_CUST. cbn [outside]. unfold SEGTOP_A in *. repeat split; try exact I; lia. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (shv_w2 sp gp w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 (sx32 e) e F4 fc4 m4 lo res jk ra s0 s1 s2 s3 s4 s5
                eq_refl ERC4 (ERRNO_ACC Σ2 m4 ART4) UT4 SHC4 FR4 ST4 HLOS ltac:(lia) SPH MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & ST5 & ERC5) & Hc5'). clear Hc5. fold usp in ST5.
  assert (MU5' : munch ([(ERRNO_A, ERRNO_A + 4)] ++ [(usp - 0, usp)]) m4 m5) by (eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ2 m4 m5 usp 0 _ ART4 ltac:(rewrite SP2, SP1; lia) ltac:(unfold USTACK_TOP in *; lia) MU5' ltac:(intros x Hx; apply client_static_intro; cbn [outside app] in Hx; lia) WM5) as ART5.
  pose proof (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(cl_fp_lia)) as CLE5.
  assert (OFF5 : forall P : Z -> Prop, (forall x, P x -> ~ (ERRNO_A <= x < ERRNO_A + 4)) -> agree_on P m4 m5).
  { intros Q HQ a Ha. apply MU5. cbn [outside]. split; [exact (HQ _ Ha) | exact I]. }
  (* [comment removed for export] *)
  apply Hk. exists Σ2, MK, SA, P, u', (sx32 e).
  split.
  2:{ split; [rewrite LV2, LV1; reflexivity|]. split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CR2, CR1; lia|]. split; [rewrite CG2; exact CG1|].
      repeat split; assumption. }
  apply (ASTA_conseq RT Σ2 PMc _ _ c5 Hc5'). intros ms5 <-. exists m5.
  split; [exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, F4, fc4; reflexivity|].
  split; [split; [exact ART5|]; split; [exact MI5|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 WM5)))) | exact ST5]|].
  split.
  { intros a Ha Ho. pose proof (cl_split RT AF Σ m usp 368 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL. unfold SHV_W in Ho. cbn [outside] in Ho.
    destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & _).
    rewrite (MU5 a ltac:(cbn [outside]; split; [exact O2 | exact I])).
    rewrite (PRES4 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; rewrite LV1; exact Hy | rewrite FRS1; intros y Hy; exact Hy | unfold usp1; lia]) ltac:(unfold SLX_W; cbn [outside]; repeat split; try exact I; lia)).
    rewrite (MU3 a ltac:(cbn [outside]; unfold usp in *; repeat split; try exact I; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros y Hy; exact Hy | intros y Hy; exact Hy | unfold usp1; lia])).
    apply PR1; [exact Ha | exact I]. }
  split; [exact CLE5|].
  assert (K5 : forall a cs, rw_cells asegs m4 a cs -> (a + Z.of_nat (cells_size cs) <= ERRNO_A \/ ERRNO_A + 4 <= a) -> rw_cells asegs m5 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m4 m5 _ _ X); [| exact WM5]. apply OFF5. intros; lia. }
  split; [exact (K5 _ _ STP4 ltac:(cbn; unfold G_IC_STOPPED; lia))|]. split; [exact (K5 _ _ OD4 ltac:(cbn; unfold G_IC_OPTSDONE; lia))|].
  split; [exact (K5 _ _ ONCE4 ltac:(cbn; unfold G_IC_BASE_ONCE; lia))|]. split; [exact (K5 _ _ BRET4 ltac:(cbn; unfold G_IC_BASE_RET; lia))|].
  split; [exact ERC5|].
  split; [exact (K5 _ _ OC4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ IC4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ KC4 ltac:(cbn; lia))|].
  split; [exact (K5 _ _ NK4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ KL4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ KJ4 ltac:(cbn; lia))|].
  split; [exact (K5 _ _ CBC4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ RES4 ltac:(cbn; unfold usp in *; lia))|].
  split; [exact (K5 _ _ SLOT4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ UC4 ltac:(cbn; lia))|].
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 MK 72 ART4 ltac:(rewrite LV2; right; right; left; reflexivity) ltac:(lia)) as MKHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 SA 32 ART4 ltac:(rewrite LV2; right; left; reflexivity) ltac:(lia)) as SAHI.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 P 128 ART4 ltac:(rewrite LV2; left; reflexivity) ltac:(lia)) as PHI.
  split; [exact (K5 _ _ MKC4 ltac:(cbn; lia))|]. split; [exact (K5 _ _ SAC4 ltac:(cbn; lia))|]. exact (K5 _ _ PC4 ltac:(cbn; lia)).
Qed.
End CShv.
