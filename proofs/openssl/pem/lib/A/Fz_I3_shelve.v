(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  intros ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo res e
    img_ut shb_ro errno_rw errno_acc stk_m lo_hi lo_room sp_top inv_m.
  pose proof (bv_unsigned_in_range 64 sp) as sp_rng. unfold bv_modulus in sp_rng. cbn [Z.of_N] in sp_rng.
  remember (bv_unsigned sp) as U eqn:U_def.
  rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- U_def.
  unfold g_shadow_memory_dynamic_address, SHB in shb_ro.
  pose proof (munch_refl [(U - 64, U)] m) as fp_m.
  pose proof (wmono_refl asegs m) as wm_m.
  assert (fp_ut : ut_fp [(U - 64, U)]) by ut_fp_lia.
  assert (fp_sh : sh_fp [(U - 64, U)]) by sh_fp_lia.
  assert (errno_al : 0xba3e48 mod 8 = 0) by reflexivity.
  th_frame 64%nat [8;8;8;8;8;8;8;8]%nat stk_m.
  do 9 zstep.
  do 5 zstep.
  eapply evt_cut; [eapply errno_location_proof; th_strip_ulit; lia|].
  intros ms_ret ->.
  th_ret_lit.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (errno_sh : ro_cells asegs mc (12205644 / 8 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (apply (acc_shadow0 mc 0xba3e48 8 12205644);
          [eapply acc_munch_sh; [exact errno_acc | exact fp_m | exact fp_sh | lia | lia] | reflexivity | lia | lia | reflexivity])
  end.
  change (12205644 / 8 + 2147450880) with 2148976585 in errno_sh.
  do 4 zstep.
  zstep. try th_if_lit.
  do 4 zstep.
  apply evt_done. exists (firstn 8 junk), m0.
  refine (conj eq_refl _).
  repeat match goal with |- _ /\ _ => split end; assumption.
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
  intros sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ev F fc m lo res nk j sh kold w oldcb canary ib old jk
    rav s0v s1v s2v s3v s4v s5v
    once0 init_ib key_old key_sh img_ut shb_ro ssp_m cb_old tsd_ro next_nk nk_rng lock_m keys_j keys_nk jw_case tsdj_rw
    res_seg res_al res_lo res_sh res_rw res_acc frame_rw stk_m lo_hi lo_room sp_top inv_m.
  pose proof (bv_unsigned_in_range 64 sp) as sp_rng. unfold bv_modulus in sp_rng. cbn [Z.of_N] in sp_rng.
  remember (bv_unsigned sp) as U eqn:U_def.
  rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- U_def.
  unfold SEGTOP_A in res_seg.
  assert (j_rng : 0 <= j < 128) by (destruct jw_case as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                 (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] m) as fp_m.
  pose proof (wmono_refl asegs m) as wm_m.
  assert (fp_ut : ut_fp [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                 (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)]) by ut_fp_lia.
  assert (fp_sh : sh_fp [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                 (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)]) by sh_fp_lia.
  zstep. th_if_lit.
  do 3 zstep.
  tcall (T_get_local_ex_first_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 3 nk j 4 sh kold w oldcb canary ib);
    try first [lia | reflexivity | eassumption | exact (proj1 tsdj_rw) | eapply ut_munch; [exact img_ut | exact fp_m | exact fp_ut]].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (res_shz : ro_cells asegs mc (res / 8 + 2147450880) [C1 (Z_to_bv 8 0)])
      by (apply (acc_shadow0 mc res 8 res);
          [eapply acc_munch_sh; [exact res_acc | exact fp_m | exact fp_sh | lia | lia]
          | exact res_al | lia | lia | rewrite Z.sub_diag; reflexivity])
  end.
  assert (res_q : 0 <= res / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  do 2 zstep.
  unfold SHB. rewrite (shadow_spell1 res) by lia.
  zstep. zstep. th_if_lit.
  clear ssp_m.
  lazymatch goal with Hs : ssp_cells _ canary |- _ => unfold ssp_cells, got_ssp, ssp_guard in Hs; destruct Hs as [ssp_got ssp_val] end.
  zstep. th_fix_lit_store.
  do 4 zstep.
  apply evt_done. do 8 eexists.
  refine (conj eq_refl _).
  repeat match goal with |- _ /\ _ => split end; try eassumption.
  unfold ssp_cells, got_ssp, ssp_guard. split; eassumption.
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
  intros sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ev e F fc m lo res jk rav s0v s1v s2v s3v s4v s5v
    ev_def errno_rw errno_acc img_ut shb_ro frame_rw stk_m lo_hi lo_room sp_top inv_m.
  subst ev.
  pose proof (bv_unsigned_in_range 64 sp) as sp_rng. unfold bv_modulus in sp_rng. cbn [Z.of_N] in sp_rng.
  remember (bv_unsigned sp) as U eqn:U_def.
  rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- U_def.
  assert (errno_sh : ro_cells asegs m 2148976585 [C1 (Z_to_bv 8 0)])
    by exact (acc_shadow0 m 0xba3e48 8 12205644 errno_acc eq_refl ltac:(lia) ltac:(lia) ltac:(reflexivity)).
  pose proof (munch_refl [(ERRNO_A, ERRNO_A + 4)] m) as fp_m.
  pose proof (wmono_refl asegs m) as wm_m.
  unfold SITE_shv_slx.
  zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 11 zstep.
  th_release frame_rw U.
  apply evt_done. eexists.
  refine (conj eq_refl _).
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Definition e_unshelve : Z := 0x1ff350.
(* [comment removed for export] *)
Definition unshelve_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo k MK SA P : Z) (pad top ne oldv : word) (j1 j2 j3 : list byte),
  tp = Z_to_bv 64 TP_A -> a0 <> Z_to_bv 64 (-1) ->
  ro_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] ->
  ro_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)] ->
  ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
  ro_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] ->
  0x10007fff8000 <= MK -> MK mod 8 = 0 -> MK + 72 <= lo -> acc asegs m MK 72 ->
  rw_cells asegs m MK [CB 24 j1; C8 (Z_to_bv 64 SA); CB 40 j2] ->
  0x10007fff8000 <= SA -> SA mod 8 = 0 -> SA + 32 <= lo -> acc asegs m SA 32 ->
  rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top ne (Z_to_bv 64 P)) ->
  0x10007fff8000 <= P -> P mod 8 = 0 -> P + 128 <= lo -> acc asegs m P 128 ->
  rw_cells asegs m P [C8 oldv; CB 120 j3] -> (SA + 32 <= P \/ P + 128 <= SA) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs
    (fun ms' => exists (t1' a1' a2' a3' top' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (SA + 8, SA + 24); (P, P + 8)] m m'
       /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
       /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 (bv_unsigned ne + sa_delta a0 oldv)) (Z_to_bv 64 P))
       /\ rw_cells asegs m' P [C8 a0; CB 120 j3])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_unshelve) fc None m (seg_rom asegs)).

Theorem unshelve_proof : unshelve_stmt.
Proof.
  unfold unshelve_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k MK SA P pad top ne oldv j1 j2 j3
    tp_def st_live once_set key_k k_rng key_shb tsd_main slot_mk mk_hi mk_al mk_room mk_acc mk_rw sa_hi sa_al sa_room sa_acc sa_rw
    p_hi p_al p_room p_acc p_rw sa_p_apart img_ut shb_ro stk_m lo_hi lo_room sp_top inv_m.
  subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as sp_rng. unfold bv_modulus in sp_rng. cbn [Z.of_N] in sp_rng.
  remember (bv_unsigned sp) as U eqn:U_def.
  rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- U_def.
  pose proof (rw_cells_head m P _ _ p_rw) as slot_old.
  pose proof (rw_cells_tail m P _ _ p_rw) as p_tail. cbn [csize Z.of_nat Pos.of_succ_nat] in p_tail.
  clear p_rw.
  pose proof (rw_cells_skip m MK [CB 24 j1] _ mk_rw) as mk_slot. cbn [cells_size csize Nat.add Z.of_nat] in mk_slot.
  pose proof (proj1 (rw_cells_head m _ _ _ mk_slot)) as mk_slot3. clear mk_slot.
  pose proof (munch_refl [(U - 112, U); (SA + 8, SA + 24); (P, P + 8)] m) as fp_m.
  pose proof (wmono_refl asegs m) as wm_m.
  assert (fp_ut : ut_fp [(U - 112, U); (SA + 8, SA + 24); (P, P + 8)]) by ut_fp_lia.
  assert (fp_sh : sh_fp [(U - 112, U); (SA + 8, SA + 24); (P, P + 8)]) by sh_fp_lia.
  unfold sa_hdr in sa_rw. unfold g_shadow_memory_dynamic_address in shb_ro.
  carve_frame 16%nat stk_m.
  change (Z.of_nat 8) with 8 in p_tail.
  change (cells_at asegs m (MK + Z.of_nat 24) [C8 (Z_to_bv 64 SA)]) with (ro_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)]) in mk_slot3.
  do 5 zstep.
  zstep.
  assert (st_ne : bv_eqb a0 (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; apply Z.eqb_neq; intros same; apply st_live; apply bv_eq; exact same).
  rewrite st_ne. cbv iota.
  do 7 zstep.
  th_release FR U.
  tcall (T_set_local_ex_steady_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN k 3 MK SA P 4 pad top ne oldv);
    try first [lia | reflexivity | eassumption | eapply ut_munch; [exact img_ut | exact fp_m | exact fp_ut]
              | eapply acc_munch_sh; [eassumption | exact fp_m | exact fp_sh | lia | lia]].
  pose proof (rw_cells_join2 _ P _ _ POST p_tail) as slot_new.
  apply evt_done. do 6 eexists.
  refine (conj eq_refl _).
  repeat match goal with |- _ /\ _ => split end; eassumption.
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
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (res fr0 nk j : Z) (e od sh kold w oldcb : word) (ib u : byte) (old : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 res ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 464 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_shelve (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) SHV_SITES SHV_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 2 < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m ERRNO_A [C4 e] ->
  rw_cells asegs m MK_ONCE [C4 z64] -> rw_cells asegs m MK_INIT [C1 ib] -> rw_cells asegs m MK_KEY [C4 kold] ->
  rw_cells asegs m (TP_A + -96) [C8 oldcb] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) -> 1 <= j ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
  In (fr0, 0%nat) (rt_frames RT Σ) -> fr0 <= res -> res + 8 <= fr0 + 56 -> res mod 8 = 0 ->
  acc asegs m res 8 -> rw_cells asegs m res [CB 8 old] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_shelve m)))
    (fun c => exists (Σ' : rts RT) (MK SA P : Z) (u' : byte),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SHV_W j res) m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ rw_cells asegs m' ERRNO_A [C4 (sx32 e)]
            /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
            /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
            /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]
            /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
            /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)] /\ rw_cells asegs m' res [C8 z64]
            /\ rw_cells asegs m' MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]
            /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))
            /\ rw_cells asegs m' P [C8 (Z_to_bv 64 (-1)); CB 120 (zeros 120)]) c
       /\ rt_live RT Σ' = (P, 128) :: (SA, 32) :: (MK, 72) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < MK /\ MK mod 16 = 0 /\ MK + 72 < USTACK_TOP
       /\ 0 < SA /\ SA mod 16 = 0 /\ SA + 32 < USTACK_TOP
       /\ 0 < P /\ P mod 16 = 0 /\ P + 128 < USTACK_TOP).

Theorem shelve_first_cps : shelve_first_stmt.
Proof using AF AFP C_ICB C_SLX ERRNO_ACC GO_mkey TSD.
  unfold shelve_first_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo outer lb canary res fr0 nk j e od sh kold w oldcb ib u old
    PMfd PMst tp_is a0_is art0 inv0 call0 deep ctx0 uw0 cgh frames_lt live_lt credit0 env0
    icstop icopts iconce icret errno0 once0 init0 key0 cb0 tp150 next0 nk_in lock0 keysj keysnk jw_alt j_pos tsdj
    fr_in fr_lo fr_hi res_al res_acc res0.
  subst tp a0.
  intros T c HA Hk.
  pose proof call0 as (stk0 & sp0_lo & stk_room & sp_cap & sp_mod).
  set (U := bv_unsigned sp) in *.
  pose proof (af_sp0_win RT AF Σ m art0) as sp0_win.
  assert (lo_hi : 0x10007fff8000 <= lo) by (unfold STACK_WIN in *; lia).
  assert (sp_hi : U <= 2 ^ 47) by (unfold USTACK_TOP in sp_cap; lia).
  pose proof (af_frames_align RT AF Σ m fr0 0%nat art0 fr_in) as (fr_mod & fr_seg).
  pose proof (af_frames_range RT AF Σ m fr0 0%nat art0 fr_in) as (fr_pos & fr_top & _ & _).
  pose proof (afp_frame_mem RT GOBJ AFP Σ m fr0 0%nat art0 fr_in) as (fr_half & fr_cap).
  change (fs_size 0) with 64 in fr_top, fr_half, fr_cap.
  assert (res_lo : res + 8 <= lo) by lia.
  assert (res_seg : SEGTOP_A <= res) by (unfold SEGTOP_A in *; lia).
  assert (res_sh : res + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= res) by lia.
  pose proof (af_client_consts RT AF Σ m art0) as (_ & shb0 & _ & _ & img0).
  pose proof (shv_w0 ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo res e
                img0 shb0 errno0 (ERRNO_ACC Σ m art0) stk0 lo_hi ltac:(unfold RT_STACK in deep; lia) sp_hi inv0) as step0.
  cl_lift step0 HA c1 HC1.
  destruct (ASTA_unpack RT Σ PMc _ c1 HC1) as (ms1 & (jk & m1 & -> & mu1 & wm1 & inv1 & frm1 & stk1) & HA1). clear HC1.
  assert (keep1 : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= U - 64 \/ U <= A) -> rw_cells asegs m1 A cs).
  { intros A cs H Hd. apply (rw_cells_agree asegs m m1 A cs H); [| exact wm1].
    intros x Hx. cbv beta in Hx. apply mu1. cbn [outside]. split; [lia | exact I]. }
  assert (art1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (U - 64) art0 ltac:(unfold STACK_WIN, RT_STACK in *; lia)); [| exact wm1].
    intros a Hna. apply mu1. cbn [outside]. split; [| exact I].
    intros Hin. apply Hna. left. unfold USTACK_TOP in *. lia. }
  cl_eu U (-64) EU1.
  assert (U_low : 12400000 <= U - 64) by (unfold RT_STACK in deep; lia).
  assert (icstop1 : rw_cells asegs m1 G_IC_STOPPED [C1 (Z_to_bv 8 0)]).
  { apply keep1; [exact icstop|]. left. cbn [cells_size csize Nat.add]. unfold G_IC_STOPPED. lia. }
  assert (icopts1 : rw_cells asegs m1 G_IC_OPTSDONE [C8 od]).
  { apply keep1; [exact icopts|]. left. cbn [cells_size csize Nat.add]. unfold G_IC_OPTSDONE. lia. }
  assert (iconce1 : rw_cells asegs m1 G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)]).
  { apply keep1; [exact iconce|]. left. cbn [cells_size csize Nat.add]. unfold G_IC_BASE_ONCE. lia. }
  assert (icret1 : rw_cells asegs m1 G_IC_BASE_RET [C4 (Z_to_bv 64 1)]).
  { apply keep1; [exact icret|]. left. cbn [cells_size csize Nat.add]. unfold G_IC_BASE_RET. lia. }
  assert (call1 : call_ok RT Σ m1 (Z_to_bv 64 (U + -64)) lo) by (cl_call_ok EU1 stk1 sp0_lo sp_mod 4).
  assert (deep1 : lo + RT_STACK + 400 <= bv_unsigned (Z_to_bv 64 (U + -64))) by (rewrite EU1; unfold RT_STACK in *; lia).
  assert (cred1 : 1 <= rt_credit RT Σ) by exact credit0.
  apply (C_ICB Σ PMc (Z_to_bv 64 SITE_shv_icb) (Z_to_bv 64 (U + -64)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 ERRNO_A)
           (Z_to_bv 64 OPT_BASE_ONLY) z64 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 res) (Z_to_bv 64 (Z.shiftr ERRNO_A 3 + SHB)) (sx32 e) (Z_to_bv 64 SHB)
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od PMfd PMst eq_refl eq_refl art1 inv1 call1
           ltac:(rewrite EU1; unfold RT_STACK, STACK_WIN in *; lia) frames_lt cred1 icstop1 icopts1 iconce1 icret1 T c1 HA1).
  intros c2 (Σ1 & HC2 & LV1 & FR1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 PMc _ c2 HC2) as (ms2 & (m2 & RS2 & (art2 & inv2 & wm2 & stk2) & pres2 & _) & HA2). clear HC2.
  destruct RS2 as (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & Fa & fca & ->).
  replace (ret_pc (Z_to_bv 64 SITE_shv_icb)) with (Z_to_bv 64 SITE_shv_icb) in HA2
    by (symmetry; apply ret_pc_even; [unfold SITE_shv_icb; lia | reflexivity]).
  rewrite EU1 in pres2, stk2.
  assert (CS : forall x, 12186000 <= x < 12343248 -> ~ (12205720 <= x < 12205728) -> ~ (12205800 <= x < 12205848) ->
                 ~ (12205856 <= x < 12205872) -> ~ (12341912 <= x < 12341920) -> ~ (12337584 <= x < 12337592) -> client_static x).
  { intros x b0 b1 b2 b3 b4 b5. split.
    - exists 12186000, 12343248. split; [cbn; right; right; left; reflexivity | lia].
    - intros (q1 & q2 & qin & qb). cbn in qin.
      destruct qin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <-; lia. }
  assert (keepA : forall A cs, rw_cells asegs m1 A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (U + -64) x) ->
            rw_cells asegs m2 A cs).
  { intros A cs H Hcs. apply (rw_cells_agree asegs m1 m2 A cs H); [| exact wm2].
    intros x Hx. cbv beta in Hx. apply pres2. exact (Hcs _ Hx). }
  assert (keepAro : forall A cs, ro_cells asegs m1 A cs ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (U + -64) x) ->
            ro_cells asegs m2 A cs).
  { intros A cs H Hcs. apply (ro_cells_agree asegs m1 m2 A cs H).
    intros x Hx. cbv beta in Hx. apply pres2. exact (Hcs _ Hx). }
  assert (keep1ro : forall A cs, ro_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= U - 64 \/ U <= A) -> ro_cells asegs m1 A cs).
  { intros A cs H Hd. apply (ro_cells_agree asegs m m1 A cs H).
    intros x Hx. cbv beta in Hx. apply mu1. cbn [outside]. split; [lia | exact I]. }
  assert (keepS : forall A cs, rw_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= U - 64 \/ U <= A) ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x) -> rw_cells asegs m2 A cs)
    by (intros A cs H Hd Hs; apply keepA; [apply keep1; assumption | intros x Hx; right; left; exact (Hs _ Hx)]).
  assert (keepSro : forall A cs, ro_cells asegs m A cs -> (A + Z.of_nat (cells_size cs) <= U - 64 \/ U <= A) ->
            (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x) -> ro_cells asegs m2 A cs)
    by (intros A cs H Hd Hs; apply keepAro; [apply keep1ro; assumption | intros x Hx; right; left; exact (Hs _ Hx)]).
  assert (once2 : rw_cells asegs m2 MK_ONCE [C4 z64]).
  { apply keepS; [exact once0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (init2 : rw_cells asegs m2 MK_INIT [C1 ib]).
  { apply keepS; [exact init0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (key2 : rw_cells asegs m2 MK_KEY [C4 kold]).
  { apply keepS; [exact key0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (cb2 : rw_cells asegs m2 (TP_A + -96) [C8 oldcb]).
  { apply keepS; [exact cb0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (tp1502 : rw_cells asegs m2 (TP_A + -150) [C1 u]).
  { apply keepS; [exact tp150 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (next2 : rw_cells asegs m2 NEXT_KEY [C4 (Z_to_bv 64 nk)]).
  { apply keepS; [exact next0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (lock2 : rw_cells asegs m2 KEY_LOCK [C4 z64; C4 z64; C4 sh]).
  { apply keepS; [exact lock0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (keysj2 : rw_cells asegs m2 (KEYS + 8 * j) [C8 z64]).
  { apply keepS; [exact keysj | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (tsdj2 : rw_cells asegs m2 (TSD_MAIN + 8 * j) [C8 z64]).
  { apply keepS; [exact tsdj | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (errno2 : rw_cells asegs m2 ERRNO_A [C4 e]).
  { apply keepS; [exact errno0 | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  assert (keysnk2 : ro_cells asegs m2 (KEYS + 8 * nk) [C8 w]).
  { apply keepSro; [exact keysnk | cbn [cells_size csize Nat.add]; left; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply CS; lia]. }
  pose proof (af_client_consts RT AF Σ1 m2 art2) as (_ & shb2 & _ & _ & img2).
  assert (keysh2 : ro_cells asegs m2 (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 4)]).
  { pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 MK_KEY 4 MK_KEY art2 GO_mkey ltac:(lia) ltac:(lia) ltac:(reflexivity)) as Hg.
    assert (E4 : (if 12186912 + 4 - 12186912 <? 8 then 12186912 + 4 - 12186912 else 0) = 4) by reflexivity.
    rewrite E4 in Hg. exact Hg. }
  assert (tsdro2 : ro_cells asegs m2 (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)]) by (apply wg_rw_ro; exact (TSD Σ1 m2 art2)).
  assert (env1 : cl_env m1 lb canary).
  { apply (cl_env_seg [(U - 64, U)] m m1 lb canary env0 mu1).
    apply cl_fp_cons; [unfold G_MALLOC_IMPL, ssp_guard, RT_STACK in *; lia | apply cl_fp_nil]. }
  assert (env2 : cl_env m2 lb canary) by (exact (cl_env_pres _ _ _ m1 m2 lb canary env1 pres2)).
  assert (ssp2 : ssp_cells m2 canary) by (exact (cl_env_ssp m2 lb canary img2 env2)).
  assert (res1 : rw_cells asegs m1 res [CB 8 old]).
  { apply keep1; [exact res0 | left; cbn [cells_size csize Nat.add]; unfold RT_STACK in *; lia]. }
  assert (res2 : rw_cells asegs m2 res [CB 8 old]).
  { apply keepA; [exact res1 | intros x Hx; cbn [cells_size csize Nat.add] in Hx;
      apply (acl_frame _ _ _ fr0 0%nat x fr_in); change (fs_size 0) with 64; lia]. }
  assert (resacc1 : acc asegs m1 res 8).
  { apply (acc_agree m m1 res 8 res_acc ltac:(lia)). intros x Hx. cbv beta in Hx. apply mu1. cbn [outside]. split; [| exact I].
    destruct (shad_slot_in_frame0 fr0 res lo (bv_unsigned x) fr_mod res_al fr_lo fr_hi ltac:(lia) res_lo ltac:(lia) lo_hi Hx) as (_ & Hlt).
    unfold RT_STACK in *. lia. }
  assert (resacc2 : acc asegs m2 res 8).
  { apply (acc_agree m1 m2 res 8 resacc1 ltac:(lia)). intros x Hx. cbv beta in Hx. apply pres2.
    apply (acl_fshadow _ _ _ fr0 0%nat (bv_unsigned x) fr_in). change (fs_size 0) with 64.
    exact (proj1 (shad_slot_in_frame0 fr0 res lo (bv_unsigned x) fr_mod res_al fr_lo fr_hi ltac:(lia) res_lo ltac:(lia) lo_hi Hx)). }
  assert (frm2 : rw_cells asegs m2 (U + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply keepA; [exact frm1 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; unfold USTACK_TOP in *; lia]. }
  pose proof (shv_w1 sp gp t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a s6 s7 s8 s9 s10 s11 t3a t4a t5a t6a (sx32 e) Fa fca m2 lo res nk j
                sh kold w oldcb canary ib old jk ra s0 s1 s2 s3 s4 s5
                once2 init2 key2 keysh2 img2 shb2 ssp2 cb2 tsdro2 next2 nk_in lock2 keysj2 keysnk2 jw_alt tsdj2
                res_seg res_al res_lo res_sh res2 resacc2 frm2 stk2 lo_hi ltac:(unfold RT_STACK in *; lia) sp_hi inv2) as step1.
  cl_lift step1 HA2 c3 HC3.
  destruct (ASTA_unpack RT Σ1 PMc _ c3 HC3) as (ms3 & (t0b & t1b & a3b & a4b & a5b & a6b & a7b & m3 & -> & mu3 & wm3 & inv3 & frm3 & stk3 & ssp3
     & once3 & init3 & key3 & cb3 & next3 & lock3 & keysj3 & tsdj3 & res3) & HA3). clear HC3.
  assert (shvfp : forall x, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (U - 368) x ->
     outside [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] x).
  { intros x Hx. cbn [outside]. repeat apply conj; try exact I; intros Hin; apply Hx.
    - left. unfold USTACK_TOP in *. lia.
    - right; left. apply CS; lia.
    - right; left. apply CS; lia.
    - right; left. apply CS; lia.
    - right; left. apply CS; lia.
    - right; left. apply CS; lia.
    - right; left. apply CS; lia.
    - apply (acl_frame _ _ _ fr0 0%nat x fr_in). change (fs_size 0) with 64. lia. }
  assert (art3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (U - 368) art2 ltac:(rewrite SP1; unfold STACK_WIN, RT_STACK in *; lia)); [| exact wm3].
    intros a Hna. apply mu3. apply shvfp. rewrite LV1, FR1 in Hna. exact Hna. }
  assert (j_rng : 0 <= j < 128) by (destruct jw_alt as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  assert (W3low : forall x, U <= x -> outside [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] x).
  { intros x Hx. cbn [outside]. repeat apply conj; try exact I; unfold RT_STACK in *; lia. }
  assert (AG3 : agree_on (fun x => U <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha.
    assert (Hge : U <= bv_unsigned a) by lia.
    pose proof (W3low (bv_unsigned a) Hge) as H3.
    assert (H2 : aclient (rt_live RT Σ) (rt_frames RT Σ) (U + -64) (bv_unsigned a)) by (left; lia).
    assert (H1 : outside [(U - 64, U)] (bv_unsigned a)) by (cbn [outside]; split; [lia | exact I]).
    rewrite (mu3 a H3), (pres2 a H2), (mu1 a H1). reflexivity. }
  assert (frmtail : rw_cells asegs m3 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { pose proof (rw_cells_skip m3 (U + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frm3) as Hs.
    cbn [cells_size csize Nat.add Z.of_nat] in Hs. replace (U + -64 + 48) with (bv_unsigned sp - 16) in Hs by lia. exact Hs. }
  assert (site_slx : In (SITE_shv_slx, e_shelve) (cg_site (rt_cg RT Σ))) by (apply (proj1 cgh); unfold SHV_SITES; left; reflexivity).
  assert (call_slx : In (SITE_shv_slx, e_slx) (cg_call (rt_cg RT Σ))) by (apply (proj2 cgh); unfold SHV_CALLS; left; reflexivity).
  assert (call_sas : In (SITE_shv_slx, e_sa_set) (cg_call (rt_cg RT Σ))) by (apply (proj2 cgh); unfold SHV_CALLS; right; left; reflexivity).
  assert (cgh_slx : cg_has (rt_cg RT Σ) SLX_SITES SLX_CALLS).
  { split; [intros x Hx; apply (proj1 cgh); unfold SHV_SITES; right; exact Hx
           | intros x Hx; apply (proj2 cgh); unfold SHV_CALLS; right; right; exact Hx]. }
  assert (spd16 : bv_unsigned (Z_to_bv 64 (U + -64)) + 16 <= bv_unsigned sp) by (rewrite EU1; lia).
  assert (sptop16 : bv_unsigned sp + 16 <= USTACK_TOP) by lia.
  destruct (cl_chain_call (rt_cg RT Σ) e_shelve e_slx SITE_shv_slx m m3 ra s0 sp (Z_to_bv 64 (U + -64)) outer
              ctx0 site_slx call_slx uw0 AG3 frmtail spd16 sptop16) as (ctx3 & uw3).
  assert (tp1503 : rw_cells asegs m3 (TP_A + -150) [C1 u]).
  { apply (rw_cells_agree asegs m2 m3 _ _ tp1502); [| exact wm3].
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply mu3. cbn [outside].
    repeat apply conj; try exact I; unfold RT_STACK, SEGTOP_A in *; lia. }
  assert (env3 : cl_env m3 lb canary).
  { apply (cl_env_seg _ m2 m3 lb canary env2 mu3).
    repeat (apply cl_fp_cons; [unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard, RT_STACK, SEGTOP_A in *; lia |]).
    apply cl_fp_nil. }
  assert (call3 : call_ok RT Σ1 m3 (Z_to_bv 64 (U + -64)) lo).
  { unfold call_ok. rewrite EU1. split; [exact stk3|]. rewrite SP1. split; [exact sp0_lo|].
    split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in sp_mod; [|lia]. destruct sp_mod as (q & Hq). exists (q - 4). lia. }
  assert (deep3 : lo + RT_STACK + 400 <= bv_unsigned (Z_to_bv 64 (U + -64))) by (rewrite EU1; unfold RT_STACK in *; lia).
  assert (slxlit : bv_unsigned (Z_to_bv 64 SITE_shv_slx) = SITE_shv_slx) by (apply unsigned_lit; unfold SITE_shv_slx; lia).
  assert (ctx3' : cg_ctx (rt_cg RT Σ1) e_slx (bv_unsigned (Z_to_bv 64 SITE_shv_slx) :: bv_unsigned ra :: outer))
    by (rewrite CG1, slxlit; exact ctx3).
  assert (call_sas3 : In (bv_unsigned (Z_to_bv 64 SITE_shv_slx), e_sa_set) (cg_call (rt_cg RT Σ1)))
    by (rewrite CG1, slxlit; exact call_sas).
  assert (cgh3 : cg_has (rt_cg RT Σ1) SLX_SITES SLX_CALLS) by (rewrite CG1; exact cgh_slx).
  assert (live3 : Z.of_nat (length (rt_live RT Σ1)) + 2 < LIVE_MAX) by (rewrite LV1; exact live_lt).
  assert (cred3 : 0 <= rt_credit RT Σ1) by lia.
  assert (a2nz : bv_unsigned (Z_to_bv 64 (-1)) <> 0) by (vm_compute; discriminate).
  assert (jr3 : 1 <= j < 128) by lia.
  apply (C_SLX Σ1 PMc (Z_to_bv 64 SITE_shv_slx) (Z_to_bv 64 (U + -64)) gp (Z_to_bv 64 TP_A) t0b t1b t2a sp (Z_to_bv 64 ERRNO_A)
           (Z_to_bv 64 3) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) a3b a4b a5b a6b a7b (Z_to_bv 64 res) (Z_to_bv 64 2148976585) (sx32 e) (Z_to_bv 64 SHB)
           s6 s7 s8 s9 s10 s11 t3a t4a t5a t6a Fa fca m3 lo (bv_unsigned ra :: outer) lb canary j u
           PMfd PMst eq_refl eq_refl eq_refl a2nz art3 inv3 call3 deep3 ctx3' uw3 call_sas3 cgh3 live3 cred3 env3
           once3 key3 jr3 tsdj3 tp1503 T c3 HA3).
  intros c4 (Σ2 & MK & SA & P & u' & HC4 & LV2 & FR2 & SP2 & CR2 & CG2 & MKpos & MKal & MKtop & SApos & SAal & SAtop & Ppos & Pal & Ptop).
  destruct (ASTA_unpack RT Σ2 PMc _ c4 HC4) as (ms4 & (m4 & RS4 & (art4 & inv4 & wm4 & stk4) & pres4 & env4 & tsdj4 & tp1504 & mk4 & sa4 & p4) & HA4). clear HC4.
  destruct RS4 as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & Fb & fcb & ->).
  replace (ret_pc (Z_to_bv 64 SITE_shv_slx)) with (Z_to_bv 64 SITE_shv_slx) in HA4
    by (symmetry; apply ret_pc_even; [unfold SITE_shv_slx; lia | reflexivity]).
  rewrite EU1 in pres4, stk4.
  pose proof (af_client_consts RT AF Σ2 m4 art4) as (_ & shb4 & _ & _ & img4).
  assert (keep4 : forall A cs, rw_cells asegs m3 A cs ->
      (forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (U + -64) x /\ outside (SLX_W j) x) ->
      rw_cells asegs m4 A cs).
  { intros A cs H Hc. apply (rw_cells_agree asegs m3 m4 A cs H); [| exact wm4].
    intros x Hx. cbv beta in Hx. destruct (Hc _ Hx) as (Hc1 & Hc2). exact (pres4 x Hc1 Hc2). }
  assert (keep3 : forall A cs, rw_cells asegs m2 A cs ->
      (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] x) ->
      rw_cells asegs m3 A cs).
  { intros A cs H Hc. apply (rw_cells_agree asegs m2 m3 A cs H); [| exact wm3].
    intros x Hx. cbv beta in Hx. exact (mu3 x (Hc _ Hx)). }
  assert (errno3 : rw_cells asegs m3 ERRNO_A [C4 e]).
  { apply keep3; [exact errno2|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside].
    repeat apply conj; try exact I; unfold RT_STACK, SEGTOP_A in *; lia. }
  assert (errno4 : rw_cells asegs m4 ERRNO_A [C4 e]).
  { apply keep4; [exact errno3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
    - right; left. apply CS; lia.
    - unfold SLX_W. cbn [outside]. repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia. }
  assert (frm4 : rw_cells asegs m4 (U + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply keep4; [exact frm3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
    - left. unfold USTACK_TOP in *. lia.
    - unfold SLX_W. cbn [outside]. repeat apply conj; try exact I; unfold G_ALLOW_CUST, RT_STACK in *; lia. }
  assert (lo64 : lo <= bv_unsigned sp - 64) by (unfold RT_STACK in *; lia).
  pose proof (shv_w2 sp gp t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c s6 s7 s8 s9 s10 s11 t3c t4c t5c t6c (sx32 e) e Fb fcb m4 lo res jk
                ra s0 s1 s2 s3 s4 s5 eq_refl errno4 (ERRNO_ACC Σ2 m4 art4) img4 shb4 frm4 stk4 lo_hi lo64 sp_hi inv4) as step2.
  cl_lift step2 HA4 c5 HC5.
  destruct (ASTA_unpack RT Σ2 PMc _ c5 HC5) as (ms5 & (m5 & -> & mu5 & wm5 & inv5 & stk5 & errno5) & HA5). clear HC5.
  assert (INMK : In (MK, 72) (rt_live RT Σ2)) by (rewrite LV2; right; right; left; reflexivity).
  assert (INSA : In (SA, 32) (rt_live RT Σ2)) by (rewrite LV2; right; left; reflexivity).
  assert (INP : In (P, 128) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 MK 72 art4 INMK) as (_ & _ & MKseg).
  pose proof (af_live_range RT AF Σ2 m4 SA 32 art4 INSA) as (_ & _ & SAseg).
  pose proof (af_live_range RT AF Σ2 m4 P 128 art4 INP) as (_ & _ & Pseg).
  unfold SEGTOP_A in MKseg, SAseg, Pseg.
  assert (keep5 : forall A cs, rw_cells asegs m4 A cs ->
      (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside [(ERRNO_A, ERRNO_A + 4)] x) -> rw_cells asegs m5 A cs).
  { intros A cs H Hc. apply (rw_cells_agree asegs m4 m5 A cs H); [| exact wm5].
    intros x Hx. cbv beta in Hx. exact (mu5 x (Hc _ Hx)). }
  assert (statics4 : forall A cs, rw_cells asegs m3 A cs ->
      (forall x, A <= x < A + Z.of_nat (cells_size cs) -> client_static x /\ outside (SLX_W j) x) -> rw_cells asegs m4 A cs).
  { intros A cs H Hc. apply keep4; [exact H|]. intros x Hx. destruct (Hc _ Hx) as (Hs & Ho). split; [right; left; exact Hs | exact Ho]. }
  assert (WM : wmono asegs m m5).
  { eapply wmono_trans; [exact wm1|]. eapply wmono_trans; [exact wm2|]. eapply wmono_trans; [exact wm3|].
    eapply wmono_trans; [exact wm4|]. exact wm5. }
  assert (art5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 U art4 ltac:(rewrite SP2, SP1; unfold STACK_WIN, RT_STACK in *; lia)); [| exact wm5].
    intros a Hna. apply mu5. cbn [outside]. split; [| exact I]. intros Hin. apply Hna. right; left. apply CS; lia. }
  assert (once5 : rw_cells asegs m5 MK_ONCE [C4 (Z_to_bv 64 2)]).
  { apply keep5; [apply statics4; [exact once3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (init5 : rw_cells asegs m5 MK_INIT [C1 (Z_to_bv 8 1)]).
  { apply keep5; [apply statics4; [exact init3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (key5 : rw_cells asegs m5 MK_KEY [C4 (Z_to_bv 64 j)]).
  { apply keep5; [apply statics4; [exact key3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (next5 : rw_cells asegs m5 NEXT_KEY [C4 (Z_to_bv 64 j)]).
  { apply keep5; [apply statics4; [exact next3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (lock5 : rw_cells asegs m5 KEY_LOCK [C4 z64; C4 z64; C4 sh]).
  { apply keep5; [apply statics4; [exact lock3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (keysj5 : rw_cells asegs m5 (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)]).
  { apply keep5; [apply statics4; [exact keysj3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (cb5 : rw_cells asegs m5 (TP_A + -96) [C8 oldcb]).
  { apply keep5; [apply statics4; [exact cb3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply CS; lia | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (res5 : rw_cells asegs m5 res [C8 z64]).
  { apply keep5; [apply keep4; [exact res3 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; split;
      [apply (acl_frame _ _ _ fr0 0%nat x); [rewrite FR1; exact fr_in | change (fs_size 0) with 64; lia]
      | unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; unfold G_ALLOW_CUST, SEGTOP_A in *; lia]]
    | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [unfold SEGTOP_A in *; lia | exact I]]. }
  assert (tsdj5 : rw_cells asegs m5 (TSD_MAIN + 8 * j) [C8 (Z_to_bv 64 MK)]).
  { apply keep5; [exact tsdj4 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (tp1505 : rw_cells asegs m5 (TP_A + -150) [C1 u']).
  { apply keep5; [exact tp1504 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (mk5 : rw_cells asegs m5 MK [CB 24 (zeros 24); C8 (Z_to_bv 64 SA); CB 40 (zeros 40)]).
  { apply keep5; [exact mk4 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (sa5 : rw_cells asegs m5 SA (sa_hdr (Z_to_bv 64 1) z64 z64 (Z_to_bv 64 1) (Z_to_bv 64 P))).
  { apply keep5; [exact sa4 | intros x Hx; unfold sa_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (p5 : rw_cells asegs m5 P [C8 (Z_to_bv 64 (-1)); CB 120 (zeros 120)]).
  { apply keep5; [exact p4 | intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; split; [lia | exact I]]. }
  assert (env5 : cl_env m5 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m4 m5 _ canary env4 mu5).
    apply cl_fp_cons; [unfold G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in *; lia | apply cl_fp_nil]. }
  assert (FP : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (SHV_W j res) m m5).
  { intros a Hacl Hout. unfold SHV_W in Hout. cbn [outside] in Hout.
    destruct Hout as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & _).
    assert (Hsp : U <= bv_unsigned a \/ bv_unsigned a < U - 368).
    { apply (cl_split RT AF Σ m U 368 (bv_unsigned a) art0); [unfold STACK_WIN, RT_STACK in *; lia | lia | exact Hacl]. }
    assert (H5 : outside [(ERRNO_A, ERRNO_A + 4)] (bv_unsigned a)) by (cbn [outside]; split; [lia | exact I]).
    assert (Hmono : aclient (rt_live RT Σ) (rt_frames RT Σ) (U + -64) (bv_unsigned a)).
    { apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) U (rt_live RT Σ) (rt_frames RT Σ) (U + -64) (bv_unsigned a) Hacl);
        [intros ee He; exact He | intros ee He; exact He | lia]. }
    assert (H4a : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (U + -64) (bv_unsigned a)) by (rewrite LV1, FR1; exact Hmono).
    assert (H4b : outside (SLX_W j) (bv_unsigned a)) by (unfold SLX_W; cbn [outside]; repeat apply conj; try exact I; lia).
    assert (H3 : outside [(U - 368, U - 64); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
              (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88); (res, res + 8)] (bv_unsigned a))
      by (cbn [outside]; repeat apply conj; try exact I; lia).
    assert (H1 : outside [(U - 64, U)] (bv_unsigned a)) by (cbn [outside]; split; [lia | exact I]).
    rewrite (mu5 a H5), (pres4 a H4a H4b), (mu3 a H3), (pres2 a Hmono), (mu1 a H1). reflexivity. }
  apply Hk. exists Σ2, MK, SA, P, u'.
  split.
  - apply (ASTA_conseq RT Σ2 PMc _ _ c5 HA5). intros ms <-. exists m5.
    split. { unfold ret_st. do 16 eexists. reflexivity. }
    split. { split; [exact art5|]. split; [exact inv5|]. split; [exact WM|]. exact stk5. }
    split; [exact FP|].
    split; [exact env5|].
    split; [exact errno5|].
    repeat match goal with |- _ /\ _ => split end; assumption.
  - rewrite LV2, LV1, FR2, FR1, SP2, SP1, CR2, CR1, CG2, CG1.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
Qed.
End CShv.
