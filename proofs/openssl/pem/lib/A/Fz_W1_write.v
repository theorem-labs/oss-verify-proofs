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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_grow Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma fl_rdonly_byte : forall fl, 0 <= fl -> Z.land fl 512 = 0 -> Z.land (Z.shiftr fl 8 mod 256) 2 = 0.
Proof.
  intros fl H0 H. change 256 with (2 ^ 8). apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 1) as [-> | NE].
  - rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. change (1 + 8) with 9.
    assert (B : Z.testbit (Z.land fl 512) 9 = false) by (rewrite H; apply Z.bits_0). rewrite Z.land_spec in B.
    change (Z.testbit 512 9) with true in B. rewrite andb_true_r in B. rewrite B. reflexivity.
  - replace (Z.testbit 2 n) with false; [apply andb_false_r|].
    symmetry. destruct (Z.eq_dec n 0) as [-> | NE0]; [reflexivity|]. change 2 with (2 ^ 1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma ldiff15 : forall fl, 0 <= fl -> Z.ldiff fl 15 = fl - fl mod 16.
Proof. intros fl H. change 15 with (Z.ones 4). rewrite Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. Z.div_mod_to_equations. lia. Qed.
Lemma and_clr15 : forall fl, 0 <= fl < 2 ^ 64 -> Z.land fl 18446744073709551600 = fl - fl mod 16.
Proof.
  intros fl H. rewrite <- ldiff15 by lia. replace 18446744073709551600 with (Z.land (Z.ones 64) (Z.lnot 15)) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
Qed.
Lemma fl_ok_clr15 : forall fl, fl_ok fl -> fl_ok (fl - fl mod 16).
Proof.
  intros fl (H1 & H2). split; [Z.div_mod_to_equations; lia|]. rewrite <- ldiff15 by lia. rewrite Z.ldiff_land.
  rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 15) 512), Z.land_assoc, H2. apply Z.land_0_l.
Qed.

Definition SITE_wr_sync : Z := 0x30419c.
Definition SITE_wr_grow : Z := 0x3041b8.
Definition SITE_wr_cpy1 : Z := 0x3041f4.
Definition SITE_wr_cpy2 : Z := 0x304210.
Definition wr_frame (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition wr_s0_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (BI BB IN inl fl blen lo : Z) (rrw numw padw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BI) (Z_to_bv 64 0) (Z_to_bv 64 fl) (Z_to_bv 64 ((BI + 48) ≫ 3))
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 BI) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 blen)
                 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_buf_sync) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (wr_frame s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)).

Lemma wr_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R IN inl fl blen : Z) (rrw numw padw dw rmw rflw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 49) [C1 (Z_to_bv 8 (fl ≫ 8))] ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m R [C8 (Z_to_bv 64 blen); C8 dw; C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BI + 128 <= BB \/ BB + 16 <= BI) -> (BI + 128 <= R \/ R + 32 <= BI) ->
  0 < IN -> IN + inl < 2^63 -> 1 <= inl < 2^31 -> 0 <= blen < 2^63 -> mem_inv asegs m ->
  evt asegs (wr_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' BI BB IN inl fl blen lo rrw numw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 IN) (Z_to_bv 64 inl) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_write) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK FB1 ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR IN0 INHI HINL HBL MI.
  unfold e_mem_write, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 10 zstep. zstep.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  do 5 zstep. zstep. th_if_lit.
  zstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. th_if_lit.         (* [comment removed for export] *)
  zstep. cbv beta. rewrite (Z_to_bv_unsigned 8 (fl ≫ 8)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  zstep. rewrite (fl_rdonly_byte fl) by lia. zstep. th_if_lit.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -80). zstep. try th_ret_lit.
  zstep. if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; lia). try clear Kb.
  zstep. if_cases Kz; zify_cond Kz; try (exfalso; rewrite ?unsigned_lit in Kz by lia; lia). try clear Kz.
  do 4 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_s0_post, SITE_wr_sync, e_mem_buf_sync, wr_frame, bio_w1_cells. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition wr_s1_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BB BM IN inl blen : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_wr_grow) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 BM) (Z_to_bv 64 (blen + inl)) a2 a3
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
                 (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_BUF_MEM_grow_clean) fc None m (seg_rom asegs).

Lemma wr_s1_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 (s5x : word)
    (F : bvmap 5 word) fc (m : mem) (BB BM R IN inl blen : Z),
  bv_unsigned sp <= 2^47 -> img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 < 2^47 ->
  0 <= blen -> 0 <= inl -> blen + inl < 2^63 -> mem_inv asegs m ->
  evt asegs (wr_s1_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc BB BM IN inl blen m)
    (MS (mkR (Z_to_bv 64 SITE_wr_sync) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) a0 a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) s5x (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
             (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_wr_sync) fc None m (seg_rom asegs)).
Proof.
  intros until blen. intros SPH UT SHC BBC ACCBB BB0 BBAL BBHI BBU HBL HINL HSUM MI.
  unfold SITE_wr_sync, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_s1_post, SITE_wr_grow, e_BUF_MEM_grow_clean. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition wr_s2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BB BM q IN inl blen : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_wr_cpy1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 (q + blen)) (Z_to_bv 64 IN) (Z_to_bv 64 inl) a3
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
                 (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs).

Lemma wr_s2_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BB BM R q IN inl blen len' : Z) (lw mw flw : word),
  bv_unsigned sp <= 2^47 -> img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 < 2^47 ->
  rw_cells asegs m BM [C8 lw; C8 (Z_to_bv 64 q); C8 mw; C8 flw] -> acc asegs m BM 32 -> 0 < BM -> BM mod 16 = 0 -> 0x10007fff8000 <= BM -> BM + 32 < 2^47 ->
  0 < len' < 2^63 -> 0 < q -> q + blen < 2^63 -> 0 <= blen -> mem_inv asegs m ->
  evt asegs (wr_s2_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc BB BM q IN inl blen m)
    (MS (mkR (Z_to_bv 64 SITE_wr_grow) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 len') a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
             (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_wr_grow) fc None m (seg_rom asegs)).
Proof.
  intros until flw. intros SPH UT SHC BBC ACCBB BB0 BBAL BBHI BBU BMC ACCBM BM0 BMAL BMHI BMU HL HQ HQB HBL MI.
  unfold SITE_wr_grow, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia). assert (BMAL8 : BM mod 8 = 0) by (clear - BMAL; Z.div_mod_to_equations; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 len') = len') by (apply unsigned_lit; lia).
  zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). try clear K0.
  zstep. zstep. th_if_lit.
  do 5 zstep. zstep. th_if_lit.
  zstep. zstep. rewrite ?(unsigned_lit q), ?(unsigned_lit blen) by lia.
  zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_s2_post, SITE_wr_cpy1, e_asan_memcpy. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition wr_s3_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (BB BM R IN inl blen : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_wr_cpy2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 inl) (Z_to_bv 64 R) (Z_to_bv 64 BM) (Z_to_bv 64 32) a3
                 a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
                 (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m (seg_rom asegs).

Lemma wr_s3_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (BB BM R IN inl blen : Z),
  bv_unsigned sp <= 2^47 -> img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 < 2^47 ->
  0 <= BM < 2^64 -> 0 <= R < 2^64 -> mem_inv asegs m ->
  evt asegs (wr_s3_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc BB BM R IN inl blen m)
    (MS (mkR (Z_to_bv 64 SITE_wr_cpy1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) a0 a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 BB) (Z_to_bv 64 IN) (Z_to_bv 64 (BB + 8)) (Z_to_bv 64 (BB ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BB + 8) ≫ 3 + 2147450880))
             (Z_to_bv 64 blen) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_wr_cpy1) fc None m (seg_rom asegs)).
Proof.
  intros until blen. intros SPH UT SHC BBC ACCBB BB0 BBAL BBHI BBU HBM HR MI.
  unfold SITE_wr_cpy1, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  zstep. zstep. th_if_lit.                                     (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_s3_post, SITE_wr_cpy2, e_asan_memcpy. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition wr_s4_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (inl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 inl) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma wr_s4_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6 (s2x s3x s4x s5x s6x s7x s8x : word)
    (F : bvmap 5 word) fc (m : mem) (inl lo : Z),
  lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -80) (wr_frame s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) -> 0 <= inl < 2^63 -> mem_inv asegs m ->
  evt asegs (wr_s4_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 F fc inl lo m)
    (MS (mkR (Z_to_bv 64 SITE_wr_cpy2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 inl) a0 a1 a2 a3
             a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_wr_cpy2) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO SPH ST UT FR HINL MI.
  unfold SITE_wr_cpy2, wr_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. do 10 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold wr_s4_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.
