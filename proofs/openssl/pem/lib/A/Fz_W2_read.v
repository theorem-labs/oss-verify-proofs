(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_read Fz_W2_puts Fz_W2_gets Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_read : Z := 0x237054.
Definition e_bio_read_intern : Z := 0x237240.
Definition SITE_br_smalloc : Z := 0x2370c0.     (* [comment removed for export] *)
Definition SITE_br_intern : Z := 0x237164.      (* [comment removed for export] *)
Definition SITE_br_release : Z := 0x2371e0.     (* [comment removed for export] *)
Definition SITE_bri_brc : Z := 0x237394.        (* [comment removed for export] *)
Definition BR_DESCR : Z := 0x3d05f.
(* [comment removed for export] *)
Definition br_ftail (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition e_bread_conv : Z := 0x238fe4.
Definition SITE_brc_read : Z := 0x239068.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition brc_frame (c0 : cell) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [c0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition brc_s0_post (sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' : word) (BI PR lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a3x : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_brc_read) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 BI) a1 a2 a3x a4 a5 a6 a7
                 (Z_to_bv 64 BI) s3' (Z_to_bv 64 0x7fff8000) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_read) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) (brc_frame (CB 8 j) s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma brc_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth : Z),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 40) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= OUT < 2^64 -> 1 <= n < 2^31 - 1 -> 0 <= PR < 2^64 -> mem_inv asegs m ->
  evt asegs (brc_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 OUT) (Z_to_bv 64 n) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' BI PR lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bread_conv) fc None m (seg_rom asegs)).
Proof.
  intros until meth. intros HLO HLOS SPH ST UT SHC HM BH ACCBI BI0 BIAL BIHI BILO MSB HOUT HN HPR MI.
  unfold e_bread_conv, g_shadow_memory_dynamic_address, bio_head in *.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  all: remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  all: pose proof (munch_refl [(SP - 64, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia; assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  all: assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  all: th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  all: zstep; do 7 zstep; zstep.
  all: zstep; zstep; zstep; zstep.
  all: zstep; if_cases Kz; zify_cond Kz; try (exfalso; rewrite ?unsigned_lit in Kz by lia; clear - Kz HN; lia); try clear Kz.
  all: zstep; zstep; zstep.
  all: zstep; if_cases Kc; zify_cond Kc; [| exfalso; rewrite ?unsigned_lit in Kc by lia; clear - Kc HN; lia].
  all: zstep; do 3 zstep; cbv beta; zstep; th_if_lit.
  all: zstep.                                                   (* [comment removed for export] *)
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold brc_s0_post, SITE_brc_read, e_mem_read, brc_frame; apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition brc_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (BI PR k fl : Z) (rrw numw padw ptrw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (PR, PR + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land fl 18446744073709551487) rrw numw padw ptrw)
    /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 k)].

Lemma brc_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI PR k fl : Z) (rrw numw padw ptrw : word) (oldb j : list byte),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) ->
  rw_cells asegs m (bv_unsigned sp + -64) (brc_frame (CB 8 j) s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw ptrw) -> 0 <= fl < 2^32 ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 < PR -> PR mod 8 = 0 -> PR + 8 <= lo ->
  (PR + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PR) -> (BI + 128 <= PR \/ PR + 8 <= BI) ->
  1 <= k < 2^31 -> mem_inv asegs m ->
  evt asegs (brc_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc BI PR k fl rrw numw padw ptrw lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 BI) s3' (Z_to_bv 64 0x7fff8000) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_brc_read) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST FR BW HFL ACCBI BI0 BIAL BIHI BILO PRC PSH PR0 PRAL PRLO PRSH PRBI HK MI.
  unfold SITE_brc_read, brc_frame, bio_w1_cells in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (PR, PR + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(BI + 48, BI + 52); (PR, PR + 8)]) by (clear - BIHI PRSH; sh_fp_lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -64)) = SP + -64) by (apply unsigned_lit; lia).
  pose proof (div8_facts PR) as QP.
  do 5 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  zstep. if_cases Kk; zify_cond Kk; try (exfalso; rewrite ?unsigned_lit in Kk by lia; clear - Kk HK; lia); try clear Kk.
  zstep. zstep. zstep.
  zstep. if_cases Kn; zify_cond Kn. { exfalso. revert Kn. rewrite ?SFModel.signed_of_Z by (clear - HK; lia). clear - HK. lia. }
  zstep. zstep. zstep.
  lazymatch goal with |- context[Z.land (Z.land (0 + - Z.b2z (?c <? Z.lxor k ?c)) ?mk) k] =>
    replace (Z.land (Z.land (0 + - Z.b2z (c <? Z.lxor k c)) mk) k) with k;
    [| change c with (2 ^ 63); change mk with (Z.ones 64);
       rewrite (zb_lxor_sign k) by lia; rewrite (Z.mod_small (k + 2 ^ 63)) by lia;
       replace (2 ^ 63 <? k + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia);
       cbn [Z.b2z]; change (Z.land (0 + - (1)) (Z.ones 64)) with (Z.ones 64);
       rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia ] end.
  rewrite (zx32_small fl) in BW by (clear - HFL; lia).
  zstep. rewrite (shr3_div PR) by lia. zstep. zstep. zstep. th_if_lit.
  zstep.
  do 8 zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold brc_s1_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  rewrite (unsigned_lit fl) in BW by (clear - HFL; lia). unfold bio_w1_cells. split; [exact BW| assumption].
Qed.

(* [comment removed for export] *)
Definition bri_frame (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bri_s0_post (sp gp tp t0 t1 t2 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' : word) (BI OUT n PR meth lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bri_brc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR)
                 (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) (Z_to_bv 64 e_bread_conv) a5 a6 a7
                 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (BI + 8))
                 (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_bread_conv) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) (bri_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma bri_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth fl : Z) (shw rrw numw padw ptrw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= OUT < 2^64 -> 0 <= n < 2^64 -> 0 <= PR < 2^64 -> mem_inv asegs m ->
  evt asegs (bri_s0_post sp gp tp t0 t1 t2 a5 a6 a7 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' BI OUT n PR meth lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bio_read_intern) fc None m (seg_rom asegs)).
Proof.
  intros until ptrw. intros HLO HLOS SPH ST UT SHC HM BH BW ACCBI BI0 BIAL BIHI BILO MSB HOUT HN HPR MI.
  unfold e_bio_read_intern, g_shadow_memory_dynamic_address, bio_head, bio_w1_cells in *.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  all: remember (bv_unsigned sp) as SP eqn:ESP; rewrite <- (Z_to_bv_bv_unsigned sp); rewrite <- ESP.
  all: pose proof (munch_refl [(SP - 96, SP)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia; assert (HWS : sh_fp [(SP - 96, SP)]) by sh_fp_lia.
  all: assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  all: th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  all: zstep; do 12 zstep; zstep.
  (* [comment removed for export] *)
  all: zstep; if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; clear - Kb BI0; lia); try clear Kb.
  all: zstep.                                                   (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: zstep; zstep; zstep; zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; zstep; zstep.
  all: zstep; if_cases Km; zify_cond Km; try (exfalso; rewrite ?unsigned_lit in Km by lia; clear - Km; lia); try clear Km.
  all: zstep.                                                   (* [comment removed for export] *)
  all: zstep.
  all: do 3 zstep; cbv beta; zstep; th_if_lit.
  all: zstep.
  all: zstep; th_if_lit.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  (* [comment removed for export] *)
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: zstep; cbv beta; zstep; th_if_lit.
  all: zstep.                                                   (* [comment removed for export] *)
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; zstep; zstep; zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold bri_s0_post, SITE_bri_brc, e_bread_conv, bri_frame; apply evt_done; eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition bri_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (BI n : Z) (nr nw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ a0 = Z_to_bv 64 1
    /\ munch [(BI + 96, BI + 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw).

Lemma bri_s1_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth : Z) (nr nw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) (bri_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m PR [C8 (Z_to_bv 64 n)] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 < PR -> PR mod 8 = 0 -> PR + 8 <= 2^47 ->
  (BI + 128 <= PR \/ PR + 8 <= BI) -> 1 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (bri_s1_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 F fc BI n nr nw lo m)
    (MS (mkR (Z_to_bv 64 SITE_bri_brc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (BI + 8))
             (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bri_brc) fc None m (seg_rom asegs)).
Proof.
  intros until nw. intros HLO HLOS SPH ST FR BH BT ACCBI BI0 BIAL BIHI BILO PRC PSH PR0 PRAL PRH PRBI HN MI.
  unfold SITE_bri_brc, bri_frame, bio_head, bio_tail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 96, BI + 104)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(BI + 96, BI + 104)]) by (clear - BIHI; sh_fp_lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -96)) = SP + -96) by (apply unsigned_lit; lia).
  pose proof (div8_facts PR) as QP.
  pose proof (bv_unsigned_in_range 64 nr) as RNR; unfold bv_modulus in RNR; cbn [Z.of_N] in RNR.
  (* [comment removed for export] *)
  zstep.                                                                              (* [comment removed for export] *)
  zstep. rewrite (shr3_div PR) by lia. zstep. th_if_lit.
  zstep. zstep. cbv beta. zstep. th_if_lit.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx BIHI BILO HLO HLOS BIAL8; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  zstep. zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. if_cases Kd; zify_cond Kd; [| exfalso; rewrite ?unsigned_lit in Kd by lia; clear - Kd HN; lia].
  (* [comment removed for export] *)
  zstep.
  do 12 zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold bri_s1_post. apply evt_done. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Definition br_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (BI OUT n : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_br_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
                 (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) (C8 (Z_to_bv 64 0) :: CB 8 j :: br_ftail s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pd).

Lemma br_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd BI OUT n : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= BI < 2^64 -> 0 <= OUT < 2^64 -> 0 <= n < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (br_s0_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BI OUT n F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_read) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros HP HPM HBI HOUT HN ST HLO HLOS SPH UT SHC UAR MI. unfold e_BIO_read, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. do 10 zstep. zstep.
  zstep.
  rewrite (land_m32_pad (SP + -96) pd) by (first [lia | replace (SP + -96) with (SP + (-3) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zstep. zstep. zstep.
  do 7 zstep.
  zstep. if_false. zstep. zstep.
  destruct (stk_split asegs _ lo (SP + -96 - pd) (SP + -96) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold br_s0_post, SITE_br_smalloc, e_stack_malloc, br_ftail. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition br_s1_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (BI OUT n : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (f lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (hj rj tj j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_br_intern) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
                 (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 (f + 32)) a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_bio_read_intern) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (bv_unsigned sp + -96 - pd, bv_unsigned sp + -80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj; CB 8 rj; CB 16 tj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) bp_shadow
    /\ rw_cells asegs m' (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pd).

Lemma br_s1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI OUT n : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) (C8 (Z_to_bv 64 0) :: CB 8 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  0 <= BI < 2^64 -> 0 <= OUT < 2^64 -> 0 <= n < 2^31 ->
  mem_inv asegs m ->
  evt asegs (br_s1_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 BI OUT n F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' f lo pd m)
    (MS (mkR (Z_to_bv 64 SITE_br_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH UT FR GAP ST FB SB HBI HOUT HN MI. unfold SITE_br_smalloc, br_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP + -96 - pd, SP + -80)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8); (SP + -96 - pd, SP + -80)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO HP; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ f [] 56 fj [] [8; 8; 8; 8; 8; 16]%nat) in FB; [| reflexivity]; cbn [mk_CB_cells app] in FB.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_true.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  - replace (SP + -96 - 0) with (SP + -96) in * by lia.
    zstep.
    pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB. cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB. clear FR; rename FRB into FR.
    zstep. zstep. zstep. rewrite (shr3_div f) by lia. zstep. zstep. zstep. zstep. zstep.
    do 3 (zstep; lfix).
    zstep. do 4 (zstep; lfix).
    zstep. do 4 (zstep; lfix).
    zstep. if_cases Ks; zify_cond Ks; try (exfalso; revert Ks; rewrite ?unsigned_lit by lia; rewrite ?SFModel.signed_of_Z by lia; clear - HN; lia).
    zstep. zstep. zstep. zstep. zstep. zstep.
    subst SP.
    unfold br_s1_post, SITE_br_intern, e_bio_read_intern, BP_MAGIC, BR_DESCR, e_BIO_read, bp_shadow.
    replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) in * by lia.
    apply evt_done; do 5 eexists; split; [reflexivity|].
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FB|]; split; [exact SB|]; split; [exact FR|]; split; assumption.
  - replace (SP + -96 - 16) with (SP + -112) in * by lia.
    destruct (stk_carve asegs _ (SP + -112) (SP + -96) 16 GAP ltac:(lia)) as [GAP' [gj GFR]]. clear GAP.
    change (Z.of_nat 16) with 16 in GAP', GFR. replace (SP + -96 - 16) with (SP + -112) in GAP', GFR by lia.
    zstep.
    pose proof (stk_of_rw_cells asegs _ _ _ GFR) as GAP. cbn [cells_size csize Nat.add] in GAP. replace (SP + -112 + Z.of_nat 16) with (SP + -96) in GAP by lia. clear GFR GAP'.
    pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB. cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB. clear FR; rename FRB into FR.
    zstep. zstep. zstep. rewrite (shr3_div f) by lia. zstep. zstep. zstep. zstep. zstep.
    do 3 (zstep; lfix).
    zstep. do 4 (zstep; lfix).
    zstep. do 4 (zstep; lfix).
    zstep. if_cases Ks; zify_cond Ks; try (exfalso; revert Ks; rewrite ?unsigned_lit by lia; rewrite ?SFModel.signed_of_Z by lia; clear - HN; lia).
    zstep. zstep. zstep. zstep. zstep. zstep.
    subst SP.
    unfold br_s1_post, SITE_br_intern, e_bio_read_intern, BP_MAGIC, BR_DESCR, e_BIO_read, bp_shadow.
    replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) in * by lia.
    apply evt_done; do 5 eexists; split; [reflexivity|].
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FB|]; split; [exact SB|]; split; [exact FR|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition br_s2_post (sp gp tp : word) (BI OUT n : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (s9 s10 s11 : word) (f lo pd : Z) (j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
                 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_br_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pd).

Lemma br_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI OUT n : Z) (hj j : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pd) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj] -> rw_cells asegs m (f + 32) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m (f / 8 + 2147450880) bp_shadow ->
  1 <= n < 2^31 ->
  mem_inv asegs m ->
  evt asegs (br_s2_post sp gp tp BI OUT n F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 f lo pd j m)
    (MS (mkR (Z_to_bv 64 SITE_br_intern) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
             s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_intern) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH FR GAP ST HDR RB SB HN MI.
  unfold SITE_br_intern, br_ftail, BP_MAGIC, bp_shadow in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  (* [comment removed for export] *)
  zstep. th_if_lit.
  zstep. rewrite (t_sx32_small n) by (clear - HN; lia). zstep.
  (* [comment removed for export] *)
  zstep. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  zstep. do 8 (zstep; lfix).
  subst SP.
  unfold br_s2_post, SITE_br_release. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition br_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 : word) (n : Z) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma br_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd n : Z) (j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= n < 2^31 ->
  stk asegs m lo (bv_unsigned sp + -96 - pd) -> stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (br_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 n F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO HN ST1 GAP FR FLG FLB MI. unfold SITE_br_release, br_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep.
  do 10 zstep.
  pose proof (stk_merge asegs _ lo (SP + -96 - pd) (SP + -96) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold br_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section CBrc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

Lemma meth_bread_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 40) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth HA [-> | ->].
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_MEM_A + 40) HA GO_memmeth ltac:(unfold M_MEM_A; lia) ltac:(unfold M_MEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_MEM_A] in X. exact X.
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 40) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.

(* [comment removed for export] *)
Definition bread_conv_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl OUT n PR meth : Z) (rrw numw padw rmaxw rflw : word) (oldb : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 PR ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 -> dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> PR mod 8 = 0 ->
  (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (PR + i)) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (PR / 8 + 2147450880) ->
  0 < PR -> PR + 8 <= lo -> (PR + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PR) -> (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= PR \/ PR + 8 <= p) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= PR / 8 + 2147450880 \/ PR / 8 + 2147450880 + 1 <= p) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 64 + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bread_conv m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((PR, PR + 8) :: RD_W BI R OUT n) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)
        /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 n)])).

Theorem bread_conv_cps : bread_conv_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl OUT n PR meth rrw numw padw rmaxw rflw oldb
    FDO MST -> -> -> -> -> HM BH INBI BIAL BW FLOK INBB BBAL BBC INR RAL RC IND NDBI NDR OFF0 HN LEN MAXB DST PRC PSH PRAL PRA PSA PR0 PRLO PRSH PRAP PSAP ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 160 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  destruct DST as (po & ko & INO & OL & OH & NPO). pose proof (af_live_range RT AF Σ m po ko ART0 INO) as (PO0 & POLO' & _).
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (clear - PO0 POLO' OL OH HN LOW NUM; unfold USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  pose proof (brc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth
                HLO1 HLOS SPH ST UT SHC HM BH ACCBI BI0 BIAL BIHI BILO (meth_bread_sh Σ m meth ART0 HM) OUTR ltac:(clear - HN LEN MAXB OFF0; lia) ltac:(clear - PR0 PRLO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a3x & j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AGL : forall a k, a + k <= lo -> agree_on (fun x => a <= x < a + k) m m1) by (intros a' k H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (fold usp in SPA; cl_call_ok EU1 ST1 LOW SPA 4).
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)))
    by (apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]).
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (_ & BBLO & _). apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; clear - BBLO LOW; lia | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw rflw)) by (apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; unfold readp_cells; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]).
  assert (DST1 : dst_blk (rt_live RT Σ) OUT n [BI; R; D]) by (exists po, ko; repeat split; assumption).
  (* [comment removed for export] *)
  apply (C_RD Σ PMc (Z_to_bv 64 SITE_brc_read) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) a3x a4 a5 a6 a7
           (Z_to_bv 64 BI) s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI BB BM R D len max off fl OUT n rrw numw padw rmaxw rflw
           FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW1 FLOK INBB BBAL BBC1 INR RAL RC1 IND NDBI NDR ltac:(clear - OFF0 HN; lia) LEN ltac:(clear - MAXB; lia) ltac:(clear - HN LEN MAXB OFF0; lia) DST1 ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BW2 & RC2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_brc_read) in Hc2' by (unfold SITE_brc_read; lia).
  replace (Z.min (len - off) n) with n in Hc2', PRES2, RC2 by (clear - HN; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> outside (RD_W BI R OUT n) (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx Ho; exact (PRES2 x Hx Ho)).
  assert (FR2 : rw_cells asegs m2 usp1 (brc_frame (CB 8 j) s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold brc_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia|]. unfold RD_W. cbn [outside].
    pose proof (af_live_range RT AF Σ m po ko ART0 INO) as (_ & POLO & _). unfold usp1 in Hx. clear - Hx BILO RLO POLO OL OH HLO1 LOW. lia. }
  assert (PRC2 : rw_cells asegs m2 PR [CB 8 oldb]).
  { apply (rw_cells_agree_nw asegs m1 m2). { apply (rw_cells_agree asegs m m1 _ _ PRC); [apply AGL; cbn [cells_size csize Nat.add]; exact PRLO| exact WM1]. }
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P2.
    - replace (bv_unsigned x) with (PR + (bv_unsigned x - PR)) by (clear; lia). apply (aclient_mono _ _ _ _ _ _ _ (PRA (bv_unsigned x - PR) ltac:(clear - Hx; lia))); [auto| auto| unfold usp1; clear; lia].
    - unfold RD_W. cbn [outside]. pose proof (PRAP _ _ INBI). pose proof (PRAP _ _ INR). pose proof (PRAP _ _ INO). clear - Hx H H0 H1 OL OH HN. lia. }
  assert (PSH2 : rw_cells asegs m2 (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree_nw asegs m1 m2). { apply (rw_cells_agree asegs m m1 _ _ PSH); [apply AGL; cbn [cells_size csize Nat.add]; clear - PRSH HLOS PR0 PRLO HLO1 SPH; Z.div_mod_to_equations; lia| exact WM1]. }
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. assert (EX : bv_unsigned x = PR / 8 + 2147450880) by (clear - Hx; lia). apply P2.
    - rewrite EX. apply (aclient_mono _ _ _ _ _ _ _ PSA); [auto| auto| unfold usp1; clear; lia].
    - unfold RD_W. cbn [outside]. rewrite EX. pose proof (PSAP _ _ INBI). pose proof (PSAP _ _ INR). pose proof (PSAP _ _ INO). clear - H H0 H1 OL OH HN. lia. }
  pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) as ACCBI2.
  (* [comment removed for export] *)
  pose proof (brc_s1_walk ra (Z_to_bv 64 SITE_brc_read) sp gp y0 y1 y2 s0 s1 s2 s3 s4 s5 h1 h2 h3 h4 h5 h6 h7 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo BI PR n (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB) oldb j
                HLO1 HLOS SPH ST2 FR2 BW2 ltac:(destruct FLOK as [F1 _]; clear - F1; Z.div_mod_to_equations; lia) ACCBI2 BI0 BIAL BIHI BILO PRC2 PSH2 PR0 PRAL PRLO PRSH (PRAP _ _ INBI) ltac:(clear - HN LEN MAXB OFF0; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & BW3 & PRC3) & Hc3'). clear Hc3.
  fold usp in ST3.
  apply Hk. eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists rmaxw2, m3.
  split; [exists v0, v1, v2, g1, g2, g3, g4, g5, g6, g7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ BI 128); [exact INBI| clear - Hin; lia].
    - replace (bv_unsigned a) with (PR + (bv_unsigned a - PR)) by (clear; lia). apply (aclient_mono _ _ _ _ _ _ _ (PRA (bv_unsigned a - PR) ltac:(clear - Hin; lia))); [auto| auto| unfold usp1; clear; lia]. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split.
  { intros x Hx Ho. cbn [outside] in Ho. destruct Ho as [HoP Ho].
    rewrite (MU3 x ltac:(cbn [outside]; unfold RD_W in Ho; cbn [outside] in Ho; clear - HoP Ho; lia)).
    rewrite (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| unfold usp1; clear; lia]) Ho).
    exact (PR1 x Hx I). }
  split; [exact BW3|].
  split; [| exact PRC3].
  apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
  apply MU3. cbn [outside]. pose proof (live_ne_apart RT AF Σ m R 32 BI 128 ART0 INR INBI ltac:(intros E; injection E; clear; lia)) as A1.
  pose proof (PRAP _ _ INR). clear - Hx A1 H. split; [lia| split; [lia| exact I]].
Qed.
End CBrc.

Section CBri.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

Lemma meth_bread2_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth HA [-> | ->].
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_MEM_A + 32) HA GO_memmeth ltac:(unfold M_MEM_A; lia) ltac:(unfold M_MEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_MEM_A] in X. exact X.
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 32) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.

(* [comment removed for export] *)
Definition bri_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl OUT n PR meth : Z) (rrw numw padw rmaxw rflw nr nw : word) (oldb : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 PR ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 -> dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> PR mod 8 = 0 ->
  (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (PR + i)) -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (PR / 8 + 2147450880) ->
  0 < PR -> PR + 8 <= lo -> (PR + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PR) -> (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= PR \/ PR + 8 <= p) ->
  (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= PR / 8 + 2147450880 \/ PR / 8 + 2147450880 + 1 <= p) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 + 64 + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bio_read_intern m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((BI + 96, BI + 104) :: (PR, PR + 8) :: RD_W BI R OUT n) m m'
        /\ rw_cells asegs m' BI (bio_head meth)
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw)
        /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)
        /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 n)])).

Theorem bri_cps : bread_conv_stmt RT -> bri_stmt.
Proof.
  intros C_BRC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl OUT n PR meth rrw numw padw rmaxw rflw nr nw oldb
    FDO MST -> -> -> -> -> HM BH INBI BIAL BW FLOK BT INBB BBAL BBC INR RAL RC IND NDBI NDR OFF0 HN LEN MAXB DST PRC PSH PRAL PRA PSA PR0 PRLO PRSH PRAP PSAP ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 256 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -96).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  destruct DST as (po & ko & INO & OL & OH & NPO). pose proof (af_live_range RT AF Σ m po ko ART0 INO) as (PO0 & POLO' & _).
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (clear - PO0 POLO' OL OH HN LOW NUM; unfold USTACK_TOP in *; lia).
  assert (PRR : 0 <= PR < 2 ^ 64) by (clear - PR0 PRLO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia).
  (* [comment removed for export] *)
  pose proof (bri_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth fl (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 BB)
                HLO1 HLOS SPH ST UT SHC HM BH BW ACCBI BI0 BIAL BIHI BILO (meth_bread2_sh Σ m meth ART0 HM) OUTR ltac:(clear - HN LEN MAXB OFF0; lia) PRR MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AGL : forall a k, a + k <= lo -> agree_on (fun x => a <= x < a + k) m m1) by (intros a' k H x Hx; cbv beta in Hx; apply MU1; cbn [outside]; clear - H Hx HLO1; lia).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (fold usp in SPA; cl_call_ok EU1 ST1 LOW SPA 6).
  assert (BH1 : rw_cells asegs m1 BI (bio_head meth)) by (apply (rw_cells_agree asegs m m1 _ _ BH); [apply AGL; unfold bio_head; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]).
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)))
    by (apply (rw_cells_agree asegs m m1 _ _ BW); [apply AGL; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]).
  assert (BT1 : rw_cells asegs m1 (BI + 72) (bio_tail nr nw)) by (apply (rw_cells_agree asegs m m1 _ _ BT); [apply AGL; unfold bio_tail; cbn [cells_size csize Nat.add]; clear - BILO; lia | exact WM1]).
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (_ & BBLO & _). apply (rw_cells_agree asegs m m1 _ _ BBC); [apply AGL; cbn [cells_size csize Nat.add]; clear - BBLO LOW; lia | exact WM1]. }
  assert (RC1 : rw_cells asegs m1 R (readp_cells len D off rmaxw rflw)) by (apply (rw_cells_agree asegs m m1 _ _ RC); [apply AGL; unfold readp_cells; cbn [cells_size csize Nat.add]; exact RLO | exact WM1]).
  assert (PRC1 : rw_cells asegs m1 PR [CB 8 oldb]) by (apply (rw_cells_agree asegs m m1 _ _ PRC); [apply AGL; cbn [cells_size csize Nat.add]; exact PRLO| exact WM1]).
  assert (PSH1 : rw_cells asegs m1 (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree asegs m m1 _ _ PSH); [apply AGL; cbn [cells_size csize Nat.add]; clear - PRSH HLOS PR0 PRLO HLO1 SPH; Z.div_mod_to_equations; lia| exact WM1]. }
  assert (DST1 : dst_blk (rt_live RT Σ) OUT n [BI; R; D]) by (exists po, ko; repeat split; assumption).
  assert (PRA1 : forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 usp1)) (PR + i)).
  { intros i Hi. rewrite EU1. apply (aclient_mono _ _ _ _ _ _ _ (PRA i Hi)); [auto| auto| unfold usp1; clear; lia]. }
  assert (PSA1 : aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 usp1)) (PR / 8 + 2147450880)).
  { rewrite EU1. apply (aclient_mono _ _ _ _ _ _ _ PSA); [auto| auto| unfold usp1; clear; lia]. }
  (* [comment removed for export] *)
  apply (C_BRC Σ PMc (Z_to_bv 64 SITE_bri_brc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) (Z_to_bv 64 e_bread_conv) a5 a6 a7
           (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (BI + 8))
           (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6 F fc m1
           lo BI BB BM R D len max off fl OUT n PR meth rrw numw padw rmaxw rflw oldb
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl HM BH1 INBI BIAL BW1 FLOK INBB BBAL BBC1 INR RAL RC1 IND NDBI NDR OFF0 HN LEN MAXB DST1 PRC1 PSH1 PRAL PRA1 PSA1 PR0 PRLO PRSH PRAP PSAP ART1 MI1 CO1
           ltac:(rewrite EU1; unfold usp1, RT_STACK in *; clear - HSTK; lia)).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BW2 & RC2 & PRC2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bri_brc) in Hc2' by (unfold SITE_bri_brc; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> outside ((PR, PR + 8) :: RD_W BI R OUT n) (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx Ho; exact (PRES2 x Hx Ho)).
  pose proof (live_ne_apart RT AF Σ m po ko BI 128 ART0 INO INBI ltac:(intros E; injection E; intros _ Ep; apply NPO; rewrite Ep; left; reflexivity)) as APOB.
  assert (FR2 : rw_cells asegs m2 usp1 (bri_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold bri_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia|]. unfold RD_W. cbn [outside].
    pose proof (af_live_range RT AF Σ m po ko ART0 INO) as (_ & POLO & _). unfold usp1 in Hx. clear - Hx BILO RLO POLO OL OH HLO1 LOW PRLO. lia. }
  assert (BH2 : rw_cells asegs m2 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ BH1). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BI 128); [exact INBI| clear - Hx; lia]|]. unfold RD_W. cbn [outside].
    pose proof (PRAP _ _ INBI). pose proof (live_ne_apart RT AF Σ m R 32 BI 128 ART0 INR INBI ltac:(intros E; injection E; clear; lia)). clear - Hx H H0 APOB OL OH HN. lia. }
  assert (BT2 : rw_cells asegs m2 (BI + 72) (bio_tail nr nw)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ BT1). intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ BI 128); [exact INBI| clear - Hx; lia]|]. unfold RD_W. cbn [outside].
    pose proof (PRAP _ _ INBI). pose proof (live_ne_apart RT AF Σ m R 32 BI 128 ART0 INR INBI ltac:(intros E; injection E; clear; lia)). clear - Hx H H0 APOB OL OH HN. lia. }
  assert (PSH2 : rw_cells asegs m2 (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ PSH1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. assert (EX : bv_unsigned x = PR / 8 + 2147450880) by (clear - Hx; lia). apply P2.
    - rewrite EX. apply (aclient_mono _ _ _ _ _ _ _ PSA); [auto| auto| unfold usp1; clear; lia].
    - unfold RD_W. cbn [outside]. rewrite EX. pose proof (PSAP _ _ INBI). pose proof (PSAP _ _ INR). pose proof (PSAP _ _ INO). clear - H H0 H1 OL OH HN PRSH PR0. Z.div_mod_to_equations. lia. }
  pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) as ACCBI2.
  (* [comment removed for export] *)
  pose proof (bri_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 h1 h2 h3 h4 h5 h6 h7 s11 y3 y4 y5 y6 F2 fc2 m2 lo BI OUT n PR meth nr nw
                HLO1 HLOS SPH ST2 FR2 BH2 BT2 ACCBI2 BI0 BIAL BIHI BILO PRC2 PSH2 PR0 PRAL ltac:(clear - PRLO HLO1 SPH; lia) (PRAP _ _ INBI) ltac:(clear - HN LEN MAXB OFF0; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & v3 & v4 & v5 & v6 & m3 & -> & _ & MU3 & WM3 & MI3 & ST3 & BT3) & Hc3'). clear Hc3.
  fold usp in ST3.
  apply Hk. eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists rmaxw2, m3.
  split; [exists v0, v1, v2, g1, g2, g3, g4, g5, g6, g7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| exact I]; intros Hin; apply Ha.
    apply (acl_live _ _ _ BI 128); [exact INBI| clear - Hin; lia]. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  assert (AG23 : forall a k, (a + k <= BI + 96 \/ BI + 104 <= a) -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H x Hx. cbv beta in Hx. apply MU3. cbn [outside]. clear - H Hx. split; [lia| exact I]. }
  split.
  { intros x Hx Ho. cbn [outside] in Ho. destruct Ho as [Ho96 Ho].
    rewrite (MU3 x ltac:(cbn [outside]; clear - Ho96; split; [lia| exact I])).
    rewrite (P2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| unfold usp1; clear; lia]) Ho).
    exact (PR1 x Hx I). }
  pose proof (live_ne_apart RT AF Σ m R 32 BI 128 ART0 INR INBI ltac:(intros E; injection E; clear; lia)) as ARB. pose proof (PRAP _ _ INBI) as APRB.
  split; [apply (rw_cells_agree asegs m2 m3 _ _ BH2); [apply AG23; unfold bio_head; cbn [cells_size csize Nat.add]; clear; lia | exact WM3]|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ BW2); [apply AG23; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear; lia | exact WM3]|].
  split; [exact BT3|].
  split; [apply (rw_cells_agree asegs m2 m3 _ _ RC2); [apply AG23; unfold readp_cells; cbn [cells_size csize Nat.add]; clear - ARB; lia | exact WM3]|].
  apply (rw_cells_agree asegs m2 m3 _ _ PRC2); [apply AG23; cbn [cells_size csize Nat.add]; clear - APRB; lia | exact WM3].
Qed.
End CBri.

Section CBread.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

(* [comment removed for export] *)
Definition bio_read_core_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl OUT n meth : Z) (rrw numw padw rmaxw rflw nr nw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 -> dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 112 + 96 + 64 + 96 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_read m)))
    (fun c => exists (Σ3 : rts RT),
       ASTA RT Σ3 PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 n) m' ms
           /\ rt_after RT Σ3 (bv_unsigned sp) lo m m'
           /\ (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> outside ((BI + 96, BI + 104) :: RD_W BI R OUT n) (bv_unsigned x) -> m' x = m x)
           /\ rw_cells asegs m' BI (bio_head meth)
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw)
           /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)) c
       /\ rt_live RT Σ3 = rt_live RT Σ /\ rt_frames RT Σ3 = rt_frames RT Σ /\ rt_sp0 RT Σ3 = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ3 /\ rt_cg RT Σ3 = rt_cg RT Σ).

Theorem bio_read_core_cps : bio_read_core_stmt.
Proof.
  pose proof (bri_cps RT AF GOBJ AFP GO_memmeth GO_secmeth (bread_conv_cps RT AF GOBJ AFP GO_memmeth GO_secmeth C_RD)) as C_BRI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl OUT n meth rrw numw padw rmaxw rflw nr nw
    FDO MST -> -> -> -> HM BH INBI BIAL BW FLOK BT INBB BBAL BBC INR RAL RC IND NDBI NDR OFF0 HN LEN MAXB DST ART0 MI0 CALL HSTK Hfr Hcr.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 112 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -96 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  destruct DST as (po & ko & INO & OL & OH & NPO). pose proof (af_live_range RT AF Σ m po ko ART0 INO) as (PO0 & POLO' & _).
  assert (POLO : po + ko <= lo) by (clear - POLO' LOW; lia). clear POLO'.
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (clear - PO0 POLO OL OH HN NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia).
  pose proof (live_ne_apart RT AF Σ m po ko BI 128 ART0 INO INBI ltac:(intros E; injection E; intros _ Ep; apply NPO; rewrite Ep; left; reflexivity)) as APOB.
  pose proof (live_ne_apart RT AF Σ m R 32 BI 128 ART0 INR INBI ltac:(intros E; injection E; clear; lia)) as ARB.
  (* [comment removed for export] *)
  pose proof (br_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd BI OUT n
                HP HPM ltac:(clear - BI0 BIHI BILO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) OUTR ltac:(clear - HN LEN MAXB OFF0; lia) ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'. unfold br_ftail in FR1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_br_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(clear - Hfr; lia) ltac:(clear - Hcr; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_br_smalloc) in Hc2' by (unfold SITE_br_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & PF).
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INBI).
  assert (INR1 : In (R, 32) (rt_live RT Σ1)) by (rewrite LV1; exact INR).
  assert (INBB1 : In (BB, 16) (rt_live RT Σ1)) by (rewrite LV1; exact INBB).
  assert (IND1 : In (D, max) (rt_live RT Σ1)) by (rewrite LV1; exact IND).
  assert (INO1 : In (po, ko) (rt_live RT Σ1)) by (rewrite LV1; exact INO).
  pose proof (PF BI 128 INBI1) as PFB. pose proof (PF R 32 INR1) as PFR. pose proof (PF po ko INO1) as PFO.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF) as [SL _].
  pose proof (SL BI 128 INBI1) as SLB. pose proof (SL R 32 INR1) as SLR. pose proof (SL po ko INO1) as SLO. clear SL PF.
  change (fs_size 0) with 64 in PFB, PFR, PFO, SLB, SLR, SLO.
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLB, SLR, SLO. unfold shad, SHB in SLB, SLR, SLO.
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (br_s1_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s6 s8 s9 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F2 fc2 m2 f lo pd BI OUT n j8 fj sj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT2 FR2 GAP2 ST2 FB2 SB2 ltac:(clear - BI0 BIHI BILO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) OUTR ltac:(clear - HN LEN MAXB OFF0; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (hj & rj & tj & j0 & m3 & -> & MU3 & WM3 & MI3 & HDR3 & SB3 & FR3 & GAP3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in MU3, GAP3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia].
    - apply acl_stack. unfold usp1, USTACK_TOP in *. lia. }
  (* [comment removed for export] *)
  assert (A03 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 112 \/ usp <= bv_unsigned x) -> m3 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU3 x ltac:(cbn [outside]; unfold usp1; clear - N1 N2 Hlt HP; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])).
    apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (AGlo : forall p q a k, In (p, q) (rt_live RT Σ) -> p <= a -> a + k <= p + q -> agree_on (fun x => a <= x < a + k) m m3).
  { intros p q a k Hin H1 H2 x Hx. cbv beta in Hx. pose proof (af_live_range RT AF Σ m p q ART0 Hin) as (_ & PL & _).
    apply A03; [apply (acl_live _ _ _ p q); [exact Hin| clear - Hx H1 H2; lia] | left; unfold RT_STACK, STACK_WIN in *; clear - Hx H2 PL LOW HSTK; lia]. }
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)).
  assert (BH3 : rw_cells asegs m3 BI (bio_head meth)) by (apply (rw_cells_agree asegs m m3 _ _ BH); [apply (AGlo BI 128 _ _ INBI); unfold bio_head; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BW3 : rw_cells asegs m3 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)))
    by (apply (rw_cells_agree asegs m m3 _ _ BW); [apply (AGlo BI 128 _ _ INBI); unfold bio_w1_cells; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BT3 : rw_cells asegs m3 (BI + 72) (bio_tail nr nw)) by (apply (rw_cells_agree asegs m m3 _ _ BT); [apply (AGlo BI 128 _ _ INBI); unfold bio_tail; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BBC3 : rw_cells asegs m3 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]) by (apply (rw_cells_agree asegs m m3 _ _ BBC); [apply (AGlo BB 16 _ _ INBB); cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (RC3 : rw_cells asegs m3 R (readp_cells len D off rmaxw rflw)) by (apply (rw_cells_agree asegs m m3 _ _ RC); [apply (AGlo R 32 _ _ INR); unfold readp_cells; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (DST1 : dst_blk (rt_live RT Σ1) OUT n [BI; R; D]) by (exists po, ko; repeat split; assumption).
  (* [comment removed for export] *)
  assert (PRC3 : rw_cells asegs m3 (f + 32) [CB 8 rj]).
  { pose proof (rw_cells_skip m3 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj] _ HDR3) as X.
    cbn [cells_size csize Nat.add app] in X. replace (f + Z.of_nat 32) with (f + 32) in X by lia. exact (rw_cells_head m3 (f + 32) _ _ X). }
  assert (ESH : (f + 32) / 8 + 2147450880 = f / 8 + 2147450880 + 4) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (PSH3 : rw_cells asegs m3 ((f + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { rewrite ESH. unfold bp_shadow in SB3. pose proof (rw_cells_skip m3 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))] _ SB3) as X.
    cbn [cells_size csize Nat.add app] in X. replace (f / 8 + 2147450880 + Z.of_nat 4) with (f / 8 + 2147450880 + 4) in X by lia. exact (rw_cells_head m3 _ _ _ X). }
  pose proof CALL as CALL'. 
  assert (CO3 : call_ok RT Σ1 m3 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  apply (C_BRI Σ1 PMc (Z_to_bv 64 SITE_br_intern) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 (f + 32)) b4 b5 b6 b7
           (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3
           lo BI BB BM R D len max off fl OUT n (f + 32) meth rrw numw padw rmaxw rflw nr nw rj
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl HM BH3 INBI1 BIAL BW3 FLOK BT3 INBB1 BBAL BBC3 INR1 RAL RC3 IND1 NDBI NDR OFF0 HN LEN MAXB DST1 PRC3 PSH3 ltac:(clear - F64; Z.div_mod_to_equations; lia)).
  { intros i Hi. rewrite EU1. apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; clear - Hi; lia]. }
  { rewrite EU1, ESH. apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; clear; lia]. }
  { clear - F0; lia. }
  { clear - FLO LOW; lia. }
  { clear - FSH; lia. }
  { intros p k Hin. pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & _ & _ & PF). pose proof (PF p k Hin) as X. change (fs_size 0) with 64 in X. clear - X. lia. }
  { intros p k Hin. rewrite ESH. pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF) p k Hin) as X. rewrite SHF in X. unfold shad, SHB in X. clear - X. lia. }
  { exact ART3. }
  { exact MI3. }
  { exact CO3. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK HP. lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (rmaxw4 & m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BH4 & BW4 & BT4 & RC4 & PRC4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_br_intern) in Hc4' by (unfold SITE_br_intern; lia).

  (* [comment removed for export] *)
  assert (P4 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned x) -> outside ((BI + 96, BI + 104) :: (f + 32, f + 32 + 8) :: RD_W BI R OUT n) (bv_unsigned x) -> m4 x = m3 x)
    by (intros x Hx Ho; exact (PRES4 x Hx Ho)).
  assert (NW4 : forall x, (usp1 <= x < usp) \/ (f <= x < f + 32) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) -> outside ((BI + 96, BI + 104) :: (f + 32, f + 32 + 8) :: RD_W BI R OUT n) x).
  { intros x Hx. unfold RD_W. cbn [outside]. unfold usp1 in Hx. clear - Hx BILO RLO POLO OL OH HN FLO LOW HSTK PFB PFR PFO SLB SLR SLO HP FSH F0. unfold RT_STACK in *.
    destruct Hx as [Hx|[Hx|Hx]]; lia. }
  assert (FR4 : rw_cells asegs m4 (usp + -96) (CB 16 j0 :: br_ftail s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). intros x Hx. cbv beta in Hx. unfold br_ftail in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P4; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM HP; lia| apply NW4; left; unfold usp1; clear - Hx HP; lia]. }
  assert (GAP4 : stk asegs m4 usp1 (usp + -96)).
  { apply (stk_agree_nw asegs m3 m4 _ _ GAP3). intros x Hx. cbv beta in Hx. apply P4; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia| apply NW4; left; clear - Hx HP; lia]. }
  assert (HDR4 : rw_cells asegs m4 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj]).
  { destruct (proj1 (rw_cells_app m3 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj] [CB 8 rj; CB 16 tj]) HDR3) as [X _].
    apply (rw_cells_agree_nw asegs m3 m4 _ _ X). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P4; [apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; clear - Hx; lia] | apply NW4; right; left; clear - Hx; lia]. }
  assert (SB4 : rw_cells asegs m4 (f / 8 + 2147450880) bp_shadow).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ SB3). intros x Hx. cbv beta in Hx. unfold bp_shadow in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P4; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; clear - Hx; lia] | apply NW4; right; right; clear - Hx; lia]. }
  assert (RB4 : rw_cells asegs m4 (f + 32) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)]).
  { apply (proj2 (Fz_T_ekit.t_cells_halves asegs m4 (f + 32) n 0 ltac:(clear - HN LEN MAXB OFF0; lia) ltac:(clear; lia))). rewrite Z.mul_0_r, Z.add_0_r. exact PRC4. }
  (* [comment removed for export] *)
  pose proof (br_s2_walk sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s9 s10 s11 v3 v4 v5 v6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F4 fc4 m4 f lo pd BI OUT n hj j0
                HP F0 F64 FIMG ltac:(clear - FLO LOW; lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                FR4 GAP4 ST4 HDR4 RB4 SB4 ltac:(clear - HN LEN MAXB OFF0; lia) MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (ra1 & w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & m5 & -> & MU5 & WM5 & MI5 & FR5 & GAP5 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, FR5, GAP5, Hc5'. fold usp1 in GAP5, ST5, Hc5'.
  assert (ART5 : ART RT Σ1 m5).
  { apply (af_frame RT AF Σ1 m4 m5 usp1 ART4 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM5].
    intros a Ha. apply MU5. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ1 m5 f 0%nat (rt_frames RT Σ) ART5 FRS1) as (Σ3 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (br_s3_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s9 s10 s11 w3 w4 w5 w6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 F4 fc4 m5 f flg lo pd n j0
                HP ltac:(fold usp; unfold RT_STACK in *; clear - HSTK; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                F0 ltac:(clear - FLO LOW; lia) FL0 ltac:(clear - FLW LOW; lia) ltac:(clear - HN LEN MAXB OFF0; lia) ST5 GAP5 FR5 FW FLC MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & FLC6) & Hc6'). clear Hc6.
  fold usp in ST6.
  destruct (REL m6 MU6 WM6 FLC6) as (ART6 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).
  (* [comment removed for export] *)
  assert (NFL1 : forall x, aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM HP; lia|].
    apply NAC. right. exact H. }
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx. apply NFL1. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]. }
  (* [comment removed for export] *)
  assert (A46 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m6 x = m4 x).
  { intros x Hx.
    destruct (newframe_apart RT AF Σ Σ1 m4 f 0%nat usp _ ART4 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU6 x ltac:(cbn [outside]; split; [pose proof (NFL _ Hx) as NE; clear - NE; lia | exact I])).
    apply MU5. cbn [outside]. clear - N1 N2. lia. }
  apply Hk. exists Σ3.
  split; [| split; [rewrite LV3; exact LV1 | split; [exact FRS3 | split; [rewrite SP3; exact SP1 | split; [rewrite CR3, CR1; clear; lia | rewrite CG3; exact CG1]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ1 Σ3 PMc _ c6 Hc6' AL3 AM3)|]. intros ms <-. exists rmaxw4, m6.
  split; [exists y0, y1, y2, h1, h2, h3, h4, h5, h6, h7, y3, y4, y5, y6, F4, fc4; reflexivity|].
  split; [exact (conj ART6 (conj MI6 (conj (wmono_trans asegs _ _ _ WM03 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6))) ST6)))|].
  split.
  { intros x Hx Ho. rewrite (A46 x Hx). cbn [outside] in Ho. destruct Ho as [Ho96 Ho].
    destruct (newframe_apart RT AF Σ Σ1 m4 f 0%nat usp _ ART4 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2). change (fs_size 0) with 64 in N1, N2.
    rewrite (P4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia])
                  ltac:(cbn [outside]; split; [exact Ho96| split; [clear - N1; lia| exact Ho]])).
    apply A03; [exact Hx|]. destruct (cl_split RT AF Σ m usp 112 _ ART0 ltac:(lia) ltac:(lia) Hx) as [Hi|Lo]; [right; exact Hi | left; exact Lo]. }
  assert (AGB : forall a k, BI <= a -> a + k <= BI + 128 -> agree_on (fun x => a <= x < a + k) m4 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply A46. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx H1 H2; lia]. }
  pose proof (wmono_trans asegs _ _ _ WM5 WM6) as WM46.
  split; [apply (rw_cells_agree asegs m4 m6 _ _ BH4); [apply AGB; unfold bio_head; cbn [cells_size csize Nat.add]; clear; lia | exact WM46]|].
  split; [apply (rw_cells_agree asegs m4 m6 _ _ BW4); [apply AGB; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; clear; lia | exact WM46]|].
  split; [apply (rw_cells_agree asegs m4 m6 _ _ BT4); [apply AGB; unfold bio_tail; cbn [cells_size csize Nat.add]; clear; lia | exact WM46]|].
  apply (rw_cells_agree asegs m4 m6 _ _ RC4); [| exact WM46]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
  apply A46. apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia].
Qed.
End CBread.
