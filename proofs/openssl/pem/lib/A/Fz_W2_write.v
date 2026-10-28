(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_writec Fz_W2_puts Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_write : Z := 0x2375b4.
Definition e_bio_write_intern : Z := 0x2375f0.
Definition e_bwrite_conv : Z := 0x238ea8.
Definition SITE_bw_intern : Z := 0x2375d0.      (* [comment removed for export] *)
Definition SITE_bwi_smalloc : Z := 0x23766c.    (* [comment removed for export] *)
Definition SITE_bwi_spilled : Z := 0x2376a0.    (* [comment removed for export] *)
Definition SITE_bwi_bwc : Z := 0x23780c.        (* [comment removed for export] *)
Definition SITE_bwi_release : Z := 0x237920.    (* [comment removed for export] *)
Definition SITE_bwc_mw : Z := 0x238f14.         (* [comment removed for export] *)
Definition BWI_DESCR : Z := 0x1a040.
(* [comment removed for export] *)
Definition bwc_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bwc_s0_post (sp gp tp t0 t1 t2 a1 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' : word) (BI PR lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a4x : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bwc_mw) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 BI) a1 a2 (Z_to_bv 64 e_mem_write) a4x a5 a6 a7
                 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_write) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) (bwc_frame s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma bwc_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI IN n PR meth : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 24) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= IN < 2^64 -> 1 <= n < 2^31 - 1 -> 0 <= PR < 2^64 -> mem_inv asegs m ->
  evt asegs (bwc_s0_post sp gp tp t0 t1 t2 (Z_to_bv 64 IN) (Z_to_bv 64 n) a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' BI PR lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 PR) a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bwrite_conv) fc None m (seg_rom asegs)).
Proof.
  intros until meth. intros HLO HLOS SPH ST UT SHC HM BH ACCBI BI0 BIAL BIHI BILO MSB HIN HN HPR MI.
  unfold e_bwrite_conv, g_shadow_memory_dynamic_address, bio_head in *.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  all: remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  all: pose proof (munch_refl [(SP - 32, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia; assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  all: assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  all: th_frame 32%nat [8; 8; 8; 8]%nat ST.
  all: zstep; do 4 zstep; zstep.
  all: zstep.                                                   (* [comment removed for export] *)
  all: zstep; zstep; zstep.                                     (* [comment removed for export] *)
  all: zstep; zstep.
  all: zstep; if_cases Kc; zify_cond Kc; [| exfalso; rewrite ?unsigned_lit in Kc by lia; clear - Kc HN; lia].
  all: zstep; do 3 zstep; cbv beta; zstep; th_if_lit.
  all: zstep.        (* [comment removed for export] *)
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold bwc_s0_post, SITE_bwc_mw, e_mem_write, bwc_frame; apply evt_done; do 2 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition bwc_s1_post (ra0 sp gp tp s0' s1' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PR n : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(PR, PR + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 n)].

Lemma bwc_s1_walk : forall ra0 ra1 sp gp tp t0 t1 t2 s0' s1' s2' a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo PR n : Z) (oldb : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) ->
  rw_cells asegs m (bv_unsigned sp + -32) (bwc_frame s2' s1' s0' ra0) ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 < PR -> PR mod 8 = 0 -> PR + 8 <= lo ->
  (PR + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PR) ->
  1 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (bwc_s1_post ra0 sp gp tp s0' s1' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PR n lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bwc_mw) fc None m (seg_rom asegs)).
Proof.
  intros until oldb. intros HLO HLOS SPH ST FR PRC PSH PR0 PRAL PRLO PRSH HN MI.
  unfold SITE_bwc_mw, bwc_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(PR, PR + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(PR, PR + 8)]) by (clear - PRSH; sh_fp_lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  pose proof (div8_facts PR) as QP.
  (* [comment removed for export] *)
  zstep.
  zstep. if_cases Kk; zify_cond Kk. { exfalso. revert Kk. rewrite ?SFModel.signed_of_Z by (clear - HN; lia). clear - HN. lia. }
  zstep.
  zstep. rewrite (shr3_div PR) by lia. zstep. zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. zstep.
  lazymatch goal with |- context[Z.land (Z.land (0 - Z.b2z (?k <? Z.lxor n ?k)) ?mk) n] =>
    replace (Z.land (Z.land (0 - Z.b2z (k <? Z.lxor n k)) mk) n) with n;
    [| change k with (2 ^ 63); change mk with (Z.ones 64);
       rewrite (zb_lxor_sign n) by lia; rewrite (Z.mod_small (n + 2 ^ 63)) by lia;
       replace (2 ^ 63 <? n + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia);
       cbn [Z.b2z]; change (Z.land (0 - 1) (Z.ones 64)) with (Z.ones 64);
       rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia ] end.
  zstep. zstep.
  do 5 zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bwc_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|assumption].
Qed.

(* [comment removed for export] *)
Definition bwi_ftail (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bwi_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (BI IN n W : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bwi_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 64) a1' a2' (Z_to_bv 64 W) a4 a5 a6 a7 s2 (Z_to_bv 64 W) s4 (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 n) s8 s9 s10 (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma bwi_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd BI IN n W : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= BI < 2^64 -> 0 <= IN < 2^64 -> 0 <= n < 2^64 -> 0 <= W < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (bwi_s0_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BI IN n W F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 W) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bio_write_intern) fc None m (seg_rom asegs)).
Proof.
  intros until W. intros HP HPM HBI HIN HN HW ST HLO HLOS SPH UT SHC UAR MI. unfold e_bio_write_intern, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP)]) by ut_fp_lia.
  th_frame 160%nat [8; 48; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. do 13 zstep. zstep.
  zstep.
  rewrite (land_m32_pad (SP + -160) pd) by (first [lia | replace (SP + -160) with (SP + (-5) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zstep. zstep.
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zstep.
  all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.
  all: zstep; if_false; zstep; zstep.
  all: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
  1: destruct (stk_split asegs _ lo (SP + -160) (SP + -160) ST ltac:(lia)) as [ST1 GAP].
  2: destruct (stk_split asegs _ lo (SP + -176) (SP + -160) ST ltac:(lia)) as [ST1 GAP].
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold bwi_s0_post, SITE_bwi_smalloc, e_stack_malloc, bwi_ftail.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; do 4 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|].
  all: split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition bwi_s1a_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd n : Z) (fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bwi_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 (Z_to_bv 64 f) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_bwi_spilled) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 152, bv_unsigned sp - 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' f [CB 56 fj] /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 8 sj].

Lemma bwi_s1a_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd n : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (bwi_s1a_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd n fj sj m)
    (MS (mkR (Z_to_bv 64 SITE_bwi_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 n) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bwi_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FIMG FLO FSH HLO HLOS SPH FR GAP ST FB SB MI. unfold SITE_bwi_smalloc, bwi_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 152, SP - 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zstep.
  1: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB.
  2: pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP.
  all: unfold bwi_s1a_post, SITE_bwi_spilled, bwi_ftail.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; do 2 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition bwi_s1b_post (sp gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (BI IN n W : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (hj rj tj j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bwi_bwc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 e_bwrite_conv) a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
            F (Z_to_bv 64 e_bwrite_conv) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (W, W + 8); (bv_unsigned sp + -160 - pd + 16, bv_unsigned sp + -160 - pd + 32)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BWI_DESCR); C8 (Z_to_bv 64 e_bio_write_intern); CB 8 hj; CB 8 rj; CB 16 tj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) bp_shadow
    /\ rw_cells asegs m' W [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 24) [C8 (Z_to_bv 64 n)]
    /\ rw_cells asegs m' (bv_unsigned sp + -160 - pd + 16) [C8 (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880))]
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma bwi_s1b_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI IN n W meth fl : Z) (shw rrw numw padw ptrw : word)
    (j fj sj wj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  rw_cells asegs m W [CB 8 wj] -> acc asegs m W 8 -> bv_unsigned sp <= W -> W mod 8 = 0 -> W + 8 <= 2^47 ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> (BI + 128 <= f \/ f + 64 <= BI) ->
  ro_cells asegs m ((meth + 16) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 <= IN < 2^64 -> 0 <= n < 2^64 ->
  mem_inv asegs m ->
  evt asegs (bwi_s1b_post sp gp tp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 BI IN n W F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd m)
    (MS (mkR (Z_to_bv 64 SITE_bwi_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 W) s4 (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 n) s8 s9 (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bwi_spilled) fc None m (seg_rom asegs)).
Proof.
  intros until wj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH UT FR GAP ST FB SB WC ACCW WLO WAL WHI HM BH BW ACCBI BI0 BIAL BIHI BILO PFB MSB HIN HN MI.
  unfold SITE_bwi_spilled, bio_head, bio_w1_cells, bwi_ftail in *.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  all: remember (bv_unsigned sp) as SP eqn:ESP.
  all: pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (W, W + 8); (SP + -160 - pd + 16, SP + -160 - pd + 32)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  all: assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (W, W + 8); (SP + -160 - pd + 16, SP + -160 - pd + 32)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO HP WLO; ut_fp_lia).
  all: assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  all: assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  all: pose proof (div8_facts f) as Q1. all: pose proof (div8_facts W) as QW.
  all: apply (rw_cells_split_CB asegs _ f [] 56 fj [] [8; 8; 8; 8; 8; 16]%nat) in FB; [| reflexivity]; cbn [mk_CB_cells app] in FB.
  (* [comment removed for export] *)
  all: do 3 zstep; zstep; rewrite (shr3_div f) by lia; do 3 zstep.
  all: do 3 (zstep; lfix).
  all: zstep; zstep; do 4 (zstep; lfix).
  all: zstep; do 4 (zstep; lfix).
  (* [comment removed for export] *)
  all: zstep; if_cases Kw; zify_cond Kw; try (exfalso; rewrite ?unsigned_lit in Kw by lia; clear - Kw WLO HLO HLOS; lia); try clear Kw.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACCW1 : acc asegs mX W 8)
      by (apply (acc_agree m mX _ _ ACCW ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx FSH SPH HLO Q1 F0 F64 FLO HLOS HP WLO WHI WAL QW; Z.div_mod_to_equations; lia) end.
  all: zstep; zstep.
  all: zstep; cbv beta; zstep; th_if_lit.
  all: zstep; lfix.
  (* [comment removed for export] *)
  all: zstep; if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; clear - Kb BI0; lia); try clear Kb.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx PFB FSH BIHI SPH BILO HLO Q1 F0 HLOS BIAL8 HP WLO WHI QW; Z.div_mod_to_equations; lia) end.
  all: zstep; zstep; zstep; zstep.
  all: cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  (* [comment removed for export] *)
  all: destruct HP as [-> | ->].
  all: try replace (SP + -160 - 0) with (SP + -160) in * by lia.
  all: try replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zstep.
  all: zstep; zstep; zstep; zstep.
  all: lazymatch type of FR with
       | rw_cells _ ?mx _ (CB 16 ?x :: _) => pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 16 x] _ FR)) as SH
       | _ => pose proof (rw_cells_head _ _ _ _ FR) as SH end.
  all: cbn [cells_size csize Nat.add] in SH.
  all: lazymatch type of FR with
       | rw_cells _ ?mx _ (CB 16 ?x :: ?c :: _) => pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [CB 16 x; c] _ FR)) as DL
       | rw_cells _ ?mx _ (?c :: _) => pose proof (rw_cells_head _ _ _ _ (rw_cells_skip mx _ [c] _ FR)) as DL end.
  all: cbn [cells_size csize Nat.add] in DL.
  all: lazymatch type of DL with
       | rw_cells _ _ (_ + Z.of_nat 24) _ => change (Z.of_nat 24) with 24 in DL
       | rw_cells _ _ (_ + Z.of_nat 8) _ => change (Z.of_nat 8) with 8 in DL; replace (SP + -160 + 8) with (SP + -176 + 24) in DL by lia end.
  all: clear ACC1; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx PFB FSH BIHI SPH BILO HLO Q1 F0 HLOS BIAL8 WLO WHI QW; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  all: zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  (* [comment removed for export] *)
  all: do 4 zstep; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: zstep; cbv beta; zstep; th_if_lit.
  all: zstep.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; zstep; zstep.
  all: lazymatch type of FR with ?T => change (id T) in FR end.
  all: lazymatch type of DL with rw_cells _ _ (?b + ?x + 24) _ => let y := eval vm_compute in (x + 24) in replace (b + x + 24) with (b + y) in DL by lia end.
  all: zstep.
  all: lazymatch type of DL with rw_cells _ _ (?b + ?y) _ => let x := eval vm_compute in (y - 24) in replace (b + y) with (b + x + 24) in DL by lia end.
  all: unfold id in FR.
  all: zstep; zstep.
  (* [comment removed for export] *)
  all: lazymatch type of FR with
       | rw_cells _ _ _ (CB 16 _ :: _) => pose proof (rw_cells_blur _ _ [_; _; _; _] _ FR) as FRB
       | _ => pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB end.
  all: cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB; clear FR; rename FRB into FR.
  all: subst SP.
  all: unfold bwi_s1b_post, SITE_bwi_bwc, e_bwrite_conv, BP_MAGIC, BWI_DESCR, e_bio_write_intern, bp_shadow.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) in * by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) in * by lia.
  all: lazymatch type of SH with
       | rw_cells _ _ (?b + Z.of_nat 16) _ => replace (b + Z.of_nat 16) with (b + 16) in SH by lia
       | rw_cells _ _ ?b _ => replace b with (bv_unsigned sp + -176 + 16) in SH by lia end.
  all: apply evt_done; do 5 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FB|]; split; [exact SB|]; split; [exact WC|]; split; [exact FR|];
       split; [exact DL|]; split; [exact SH|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition bwi_s2_post (sp gp tp : word) (BI IN n W : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd : Z) (j : list byte) (nr nw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) a7
                 (Z_to_bv 64 f) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_bwi_release) fc None m' (seg_rom asegs)
    /\ munch [(BI + 104, BI + 112); (W, W + 8); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ rw_cells asegs m' W [C8 (Z_to_bv 64 n)]
    /\ rw_cells asegs m' (BI + 72) (bio_tail nr (Z_to_bv 64 (bv_unsigned nw + n)))
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma bwi_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI IN n W meth : Z) (hj j : list byte) (nr nw w0 : word),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m (bv_unsigned sp + -160 - pd + 24) [C8 (Z_to_bv 64 n)] ->
  rw_cells asegs m (bv_unsigned sp + -160 - pd + 16) [C8 (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880))] ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BWI_DESCR); C8 (Z_to_bv 64 e_bio_write_intern); CB 8 hj] -> rw_cells asegs m (f + 32) [C8 (Z_to_bv 64 n)] ->
  rw_cells asegs m (f / 8 + 2147450880) bp_shadow ->
  rw_cells asegs m W [C8 w0] -> acc asegs m W 8 -> bv_unsigned sp <= W -> W mod 8 = 0 -> W + 8 <= 2^47 ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> (BI + 128 <= f \/ f + 64 <= BI) ->
  1 <= n < 2^31 -> 0 <= IN < 2^64 ->
  mem_inv asegs m ->
  evt asegs (bwi_s2_post sp gp tp BI IN n W F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd j nr nw m)
    (MS (mkR (Z_to_bv 64 SITE_bwi_bwc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 W) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 IN) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bwi_bwc) fc None m (seg_rom asegs)).
Proof.
  intros until w0. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH FR DL SH GAP ST HDR LW SB WC ACCW WLO WAL WHI BH BT ACCBI BI0 BIAL BIHI BILO PFB HN HIN MI.
  unfold SITE_bwi_bwc, bio_head, bio_tail, bwi_ftail, BP_MAGIC, bp_shadow in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(BI + 104, BI + 112); (W, W + 8); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  pose proof (div8_facts f) as Q1. pose proof (div8_facts W) as QW.
  pose proof (bv_unsigned_in_range 64 nw) as RNW; unfold bv_modulus in RNW; cbn [Z.of_N] in RNW.
  (* [comment removed for export] *)
  zstep. zstep. th_if_lit.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx PFB FSH BIHI SPH BILO HLO Q1 F0 HLOS BIAL8 WLO WHI QW; Z.div_mod_to_equations; lia);
    assert (ACCW1 : acc asegs mX W 8)
      by (apply (acc_agree m mX _ _ ACCW ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx FSH SPH HLO Q1 F0 F64 FLO HLOS HP WLO WHI WAL QW BIHI; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  zstep. zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  (* [comment removed for export] *)
  zstep. if_cases Kw; zify_cond Kw; try (exfalso; rewrite ?unsigned_lit in Kw by lia; clear - Kw WLO HLO HLOS; lia); try clear Kw.
  zstep. zstep. zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  zstep. do 8 (zstep; lfix).
  subst SP.
  unfold bwi_s2_post, SITE_bwi_release. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition bwi_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma bwi_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd : Z) (j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -160 - pd) -> stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) ->
  rw_cells asegs m (bv_unsigned sp + -160) (CB 56 j :: bwi_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (bwi_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bwi_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_bwi_release, bwi_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep. zstep.
  do 13 zstep.
  pose proof (stk_merge asegs _ lo (SP + -160 - pd) (SP + -160) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bwi_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition bw_s0_post (sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (BI IN n : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j0 j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bw_intern) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) (Z_to_bv 64 (bv_unsigned sp + -24)) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_bio_write_intern) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j0; CB 8 j8; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma bw_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI IN n : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) ->
  1 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (bw_s0_post sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BI IN n F fc ra0 s0' lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_write) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros HLO HLOS SPH ST HN MI. unfold e_BIO_write in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. zstep. zstep. zstep.
  zstep. if_cases Kn; zify_cond Kn; try (exfalso; revert Kn; rewrite ?unsigned_lit by lia; rewrite ?SFModel.signed_of_Z by lia; clear - HN; lia).
  zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bw_s0_post, SITE_bw_intern, e_bio_write_intern. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR| assumption].
Qed.

(* [comment removed for export] *)
Definition bw_s1_post (ra0 sp gp tp s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (n : Z) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma bw_s1_walk : forall ra0 ra1 sp gp tp t0 t1 t2 s0' s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo n : Z) (j0 : list byte),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j0; C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0); C8 s0'; C8 ra0] ->
  1 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (bw_s1_post ra0 sp gp tp s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n F fc lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bw_intern) fc None m (seg_rom asegs)).
Proof.
  intros until j0. intros HLO HLOS SPH ST FR HN MI. unfold SITE_bw_intern in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep. th_if_lit.
  zstep. rewrite (t_sx32_small n) by (clear - HN; lia). zstep.
  zstep. zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bw_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition bw0_post (ra0 sp gp tp s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma bw0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo n : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) ->
  - 2 ^ 31 <= n <= 0 -> mem_inv asegs m ->
  evt asegs (bw0_post ra0 sp gp tp s0' s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1 a0 a1 (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_write) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros HLO HLOS SPH ST HN MI. unfold e_BIO_write in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 32, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 32, SP)]) by sh_fp_lia.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. zstep. zstep. zstep.
  zstep. if_cases Kn; zify_cond Kn.
  2: { exfalso. change 18446744073709551615 with (Z.ones 64) in Kn0, Kn1. rewrite Z.land_ones in Kn0, Kn1 by (clear; lia). clear - Kn0 Kn1 HN. Z.div_mod_to_equations. lia. }
  zstep. zstep. zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bw0_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
