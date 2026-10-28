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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_grow Fz_W1_write Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma fl_readp_sel : forall fl, 0 <= fl -> Z.land fl 512 = 0 -> Z.land (Z.shiftr (Z.lxor fl 18446744073709551615) 6) 8 = 8.
Proof.
  intros fl H0 H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 3) as [-> | NE].
  - rewrite Z.shiftr_spec, Z.lxor_spec by lia. change (3 + 6) with 9.
    assert (B : Z.testbit (Z.land fl 512) 9 = false) by (rewrite H; apply Z.bits_0). rewrite Z.land_spec in B.
    change (Z.testbit 512 9) with true in B. rewrite andb_true_r in B. rewrite B. reflexivity.
  - change 8 with (2 ^ 3). rewrite Z.pow2_bits_eqb by lia. replace (3 =? n) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma lor9_clr15 : forall fl, 0 <= fl -> Z.lor (fl - fl mod 16) 9 = fl - fl mod 16 + 9.
Proof.
  intros fl H. assert (D : Z.land (fl - fl mod 16) 9 = 0).
  { rewrite <- ldiff15, Z.ldiff_land by lia. rewrite <- Z.land_assoc. change (Z.land (Z.lnot 15) 9) with 0. apply Z.land_0_r. }
  rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sextw_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 (z + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia.
Qed.

Definition SITE_rd_cpy : Z := 0x304410.
Definition rd_frame (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition rd_s0_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (BI BB R OUT outl fl ret doff lo : Z) (rrw numw padw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_rd_cpy) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 (R + 8)) (Z_to_bv 64 OUT) (Z_to_bv 64 doff) (Z_to_bv 64 ret) (Z_to_bv 64 ((BI + 48) ≫ 3))
                 a4 a5 a6 a7 (Z_to_bv 64 ret) (Z_to_bv 64 R) (Z_to_bv 64 OUT) (Z_to_bv 64 outl) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (R ≫ 3 + 2147450880))
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (CB 8 j :: rd_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)).

Local Ltac rd_s0_tail SP :=
  let Ko := fresh "Ko" in let Kr := fresh "Kr" in
  zstep; if_cases Ko; zify_cond Ko; try (exfalso; rewrite ?unsigned_lit in Ko by lia; lia); try clear Ko;
  zstep; if_cases Kr; zify_cond Kr; try (exfalso; rewrite ?unsigned_lit in Kr by lia; lia); try clear Kr;
  do 4 zstep; zstep; th_if_lit;
  zstep; zstep; zstep; zstep;
  subst SP; rewrite ?Z_to_bv_bv_unsigned;
  unfold rd_s0_post, SITE_rd_cpy, e_asan_memcpy, rd_frame, bio_w1_cells; apply evt_done; do 2 eexists; split; [reflexivity|];
  split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [eassumption|]; split; assumption.

Lemma rd_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R OUT outl fl blen doff ret : Z) (rrw numw padw rmw rflw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m R [C8 (Z_to_bv 64 blen); C8 (Z_to_bv 64 doff); C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BI + 128 <= BB \/ BB + 16 <= BI) -> (BI + 128 <= R \/ R + 32 <= BI) ->
  0 < OUT -> OUT + outl < 2^63 -> 0 < outl < 2^31 -> 0 < blen < 2^63 -> 0 <= doff < 2^63 -> ret = Z.min blen outl -> mem_inv asegs m ->
  evt asegs (rd_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' BI BB R OUT outl fl ret doff lo rrw numw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 outl) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_read) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR OUT0 OUTHI HOUTL HBL HDO HRET MI.
  unfold e_mem_read, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  do 5 zstep. zstep. th_if_lit.                                (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. zstep. rewrite (fl_readp_sel fl) by lia.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -80). zstep. try th_ret_lit.
  zstep. zstep. if_cases Kn; zify_cond Kn; try (exfalso; rewrite ?unsigned_lit in Kn by lia; lia). try clear Kn.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
  - rewrite (Z.min_l blen outl) in HRET by lia. subst ret. rd_s0_tail SP.
  - rewrite (Z.min_r blen outl) in HRET by lia. subst ret. zstep. rd_s0_tail SP.
Qed.

(* [comment removed for export] *)
Definition rd_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (R blen doff ret lo : Z) (rflw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rmw' : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(R, R + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' R [C8 (Z_to_bv 64 (blen - ret)); C8 (Z_to_bv 64 (doff + ret)); C8 rmw'; C8 rflw].

Lemma rd_s1_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo R OUT outl blen doff ret : Z) (rmw rflw : word) (j : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -80) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -80) (CB 8 j :: rd_frame s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m R [C8 (Z_to_bv 64 blen); C8 (Z_to_bv 64 doff); C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  0 < ret < 2^31 -> ret <= blen -> blen < 2^63 -> 0 < doff -> doff + ret < 2^63 -> mem_inv asegs m ->
  evt asegs (rd_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc R blen doff ret lo rflw m)
    (MS (mkR (Z_to_bv 64 SITE_rd_cpy) (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (R + 8)) a0 a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 ret) (Z_to_bv 64 R) (Z_to_bv 64 OUT) (Z_to_bv 64 outl) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (R ≫ 3 + 2147450880))
             s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_rd_cpy) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH ST UT SHC FR RC ACCR R0 RAL RHI RLO HRET HRB HBL HDO HDR MI.
  unfold SITE_rd_cpy, g_shadow_memory_dynamic_address, rd_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(R, R + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(R, R + 24)]) by ut_fp_lia. assert (HWS : sh_fp [(R, R + 24)]) by sh_fp_lia.
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. rewrite ?(unsigned_lit doff), ?(unsigned_lit ret) by lia. zstep.          (* [comment removed for export] *)
  zstep. zstep.                                                                                          (* [comment removed for export] *)
  zstep. rewrite (sextw_small ret) by lia.
  do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rd_s1_post. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| eassumption].
Qed.

(* [comment removed for export] *)
Definition rd_eof_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BI BB fl lo : Z) (rrw padw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16 + 9) rrw (Z_to_bv 64 4294967295) padw (Z_to_bv 64 BB)).

Lemma rd_eof_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R OUT outl fl : Z) (rrw padw dw rmw rflw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw (Z_to_bv 64 4294967295) padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m R [C8 (Z_to_bv 64 0); C8 dw; C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BI + 128 <= BB \/ BB + 16 <= BI) -> (BI + 128 <= R \/ R + 32 <= BI) ->
  0 < OUT -> OUT + outl < 2^63 -> 0 < outl < 2^31 -> mem_inv asegs m ->
  evt asegs (rd_eof_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 F fc BI BB fl lo rrw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 outl) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_read) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR OUT0 OUTHI HOUTL MI.
  unfold e_mem_read, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (SP - 96, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 9 zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  do 5 zstep. zstep. th_if_lit.                                (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. zstep. rewrite (fl_readp_sel fl) by lia.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -80). zstep. try th_ret_lit.
  zstep. zstep. if_cases Kn; zify_cond Kn; try (exfalso; rewrite ?unsigned_lit in Kn by lia; lia). try clear Kn.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. if_cases Km; zify_cond Km; try (exfalso; rewrite ?unsigned_lit in Km by lia; lia). try clear Km.
  zstep. if_cases Ko; zify_cond Ko; try (exfalso; rewrite ?unsigned_lit in Ko by lia; lia). try clear Ko.
  zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small (fl - fl mod 16)) by (clear - FLR; Z.div_mod_to_equations; lia). zstep. rewrite ?(unsigned_lit (fl - fl mod 16)) by (clear - FLR; Z.div_mod_to_equations; lia).
  rewrite (lor9_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -80). zstep. try th_ret_lit.
  zstep. do 9 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold rd_eof_post, bio_w1_cells. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition dst_blk (live : list (Z * Z)) (OUT n : Z) (ex : list Z) : Prop :=
  exists p k, In (p, k) live /\ p <= OUT /\ OUT + n <= p + k /\ ~ In p ex.

Section CRd.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.

Definition RD_W (BI R OUT ret : Z) : list (Z * Z) := [(BI + 48, BI + 52); (R, R + 24); (OUT, OUT + ret)].

(* [comment removed for export] *)
Definition read_data_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl OUT outl : Z) (rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 outl ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off < len -> len <= max -> max < 2 ^ 31 -> 0 < outl < 2 ^ 31 -> dst_blk (rt_live RT Σ) OUT outl [BI; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_read m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.min (len - off) outl)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (RD_W BI R OUT (Z.min (len - off) outl)) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' R (readp_cells len D (off + Z.min (len - off) outl) rmaxw' rflw)
        /\ (exists bsr : list byte, bytes_at asegs m (D + off) bsr /\ Z.of_nat (length bsr) = Z.min (len - off) outl /\ bytes_at asegs m' OUT bsr))).

Theorem read_data_cps : read_data_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl OUT outl rrw numw padw rmaxw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INR RAL RC IND NDBI NDR HOFF HLEN HMAX HOUTL DST ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (blen := len - off) in *. set (ret := Z.min blen outl) in *.
  assert (HRET : 0 < ret <= blen /\ ret <= outl) by (subst ret blen; clear - HOFF HOUTL; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (D0 & DLO' & _). assert (DLO : D + max <= lo) by (clear - DLO' LOW; lia). clear DLO'.
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  pose proof (live_ne_apart RT AF Σ m D max R 32 ART0 IND INR ltac:(intros E; injection E; intros _; exact NDR)) as APDR.
  destruct DST as (p & k & INP & PL & PH & PNE).
  assert (NPI : p <> BI) by (intros ->; apply PNE; left; reflexivity). assert (NPR : p <> R) by (intros ->; apply PNE; right; left; reflexivity).
  assert (NPD : p <> D) by (intros ->; apply PNE; do 2 right; left; reflexivity). clear PNE.
  pose proof (af_live_range RT AF Σ m p k ART0 INP) as (P0 & PLO' & _). assert (PLO : p + k <= lo) by (clear - PLO' LOW; lia). clear PLO'.
  pose proof (live_ne_apart RT AF Σ m p k BI 128 ART0 INP INBI ltac:(intros E; injection E; intros _; exact NPI)) as APPI.
  pose proof (live_ne_apart RT AF Σ m p k R 32 ART0 INP INR ltac:(intros E; injection E; intros _; exact NPR)) as APPR.
  pose proof (live_ne_apart RT AF Σ m p k D max ART0 INP IND ltac:(intros E; injection E; intros _; exact NPD)) as APPD.
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 5). lia. }
  unfold readp_cells in RC.
  (* [comment removed for export] *)
  pose proof (rd_s0_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R OUT outl fl blen (D + off) ret rrw numw padw rmaxw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR
                ltac:(clear - P0 PL; lia) ltac:(clear - PH PLO HLO1 SPH; lia) HOUTL ltac:(clear - HOFF HLEN HMAX; subst blen; lia) ltac:(clear - D0 DLO HLO1 SPH HOFF HLEN; lia) eq_refl MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & BW1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 96) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> m1 x = m x).
  { intros x Hx HnF. apply MU1. cbn [outside]. split; [clear - HnF; lia | split; [| exact I]]. destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  destruct (live_CB RT AF Σ m1 D max ART1 IND ltac:(clear - HOFF HLEN; lia)) as (junk & LJ & DC1).
  pose proof (proj2 (proj1 DC1)) as DB1. cbn [cells_bytes cbytes] in DB1. rewrite app_nil_r in DB1.
  (* [comment removed for export] *)
  set (bs := firstn (Z.to_nat ret) (skipn (Z.to_nat off) junk)).
  assert (LF : Z.of_nat (length bs) = ret) by (subst bs; rewrite length_firstn, length_skipn, LJ; clear - HRET HOFF HLEN; subst ret blen; lia).
  assert (SRC1 : bytes_at asegs m1 (D + off) bs).
  { destruct DB1 as (DB0 & DBH & DBI). rewrite LJ in DBH. split; [clear - D0 HOFF; lia|]. split; [rewrite LF; clear - DBH HRET HOFF HLEN; subst ret blen; lia|].
    intros i Hi. subst bs. rewrite nth_error_firstn. replace (i <? Z.to_nat ret)%nat with true by (symmetry; apply Nat.ltb_lt; clear - Hi LF HRET; lia). rewrite nth_error_skipn.
    rewrite <- (DBI (Z.to_nat off + i)%nat ltac:(rewrite LJ; clear - Hi LF HRET HOFF HLEN; subst ret blen; lia)). f_equal. f_equal. clear - HOFF. lia. }
  apply (MCP Σ PMc (Z_to_bv 64 SITE_rd_cpy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (R + 8)) (Z_to_bv 64 OUT) (Z_to_bv 64 (D + off)) (Z_to_bv 64 ret) (Z_to_bv 64 ((BI + 48) ≫ 3))
           a4 a5 a6 a7 (Z_to_bv 64 ret) (Z_to_bv 64 R) (Z_to_bv 64 OUT) (Z_to_bv 64 outl) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (R ≫ 3 + 2147450880))
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 OUT (D + off) bs lo FDO MST eq_refl eq_refl ltac:(rewrite LF; reflexivity)
           ltac:(clear - P0 PL PH PLO HLO1 SPH HOUTL; lia) ltac:(clear - D0 DLO HLO1 SPH HOFF HLEN; lia) ltac:(rewrite LF; clear - HRET HOUTL; lia) SRC1).
  { rewrite LF. split; [intros _; split; [exact (acc_sub asegs m1 D max (D + off) ret (proj2 (af_acc_live RT AF Σ m1 D max ART1 IND)) ltac:(clear - HOFF; lia) ltac:(clear - HRET HLEN; subst blen; lia)) |
                              left; exists D, max; split; [exact IND | clear - HOFF HRET HLEN; subst blen; lia]] | left; clear - DLO HRET HOFF HLEN; subst blen; lia]. }
  { rewrite LF. exact (live_checked_dst RT AF Σ m1 _ p k OUT ret ART1 INP PL ltac:(clear - PH HRET; lia) ltac:(clear - HRET; lia)). }
  { rewrite LF. clear - APPD PL PH HRET HOFF HLEN. subst blen. lia. }
  { exact ART1. } { exact MI1. } { exact CO1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & OB2) & Hc2'). clear Hc2.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite LF in PRES2. rewrite (ret_pc_even SITE_rd_cpy) in Hc2' by (unfold SITE_rd_cpy; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> ~ (OUT <= bv_unsigned x < OUT + ret) -> m2 x = m x).
  { intros x Hx HnF HnO. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) HnO). exact (P1 x Hx HnF). }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 j :: rd_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold rd_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold usp1 in Hx; clear - Hx PLO PH HLO1 HRET; lia]. }
  assert (RC2 : rw_cells asegs m2 R [C8 (Z_to_bv 64 blen); C8 (Z_to_bv 64 (D + off)); C8 rmaxw; C8 rflw]).
  { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P2; [apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia] | clear - Hx APIR; lia | clear - Hx APPR PL PH HRET; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2). pose proof (proj2 (af_acc_live RT AF Σ m2 R 32 ART2 INR)) as ACCR2.
  (* [comment removed for export] *)
  pose proof (rd_s1_walk ra sp gp y0 y1 y2 s0 s1 (Z_to_bv 64 OUT) h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F2 fc2 m2 lo R OUT outl blen (D + off) ret rmaxw rflw j
                ltac:(clear - HLO1; lia) HLOS SPH ST2 UT2 SHC2 FR2 RC2 ACCR2 R0 RAL RHI RLO ltac:(clear - HRET HOUTL; lia) ltac:(clear - HRET; lia)
                ltac:(clear - HOFF HLEN HMAX; subst blen; lia) ltac:(clear - D0 HOFF; lia) ltac:(clear - D0 DLO HLO1 SPH HOFF HLEN HRET; subst blen; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  apply Hk. eapply ASTA_conseq; [exact Hc3|]. intros ms (z0 & z1 & z2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z3 & z4 & z5 & z6 & rmw' & m3 & -> & MU3 & WM3 & MI3 & ST3 & RC3).
  fold usp in ST3. exists rmw', m3. split; [do 16 eexists; reflexivity|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ R 32); [exact INR | clear - Hin; lia]. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split.
  { intros x Hx Ho. unfold RD_W in Ho. cbn [outside] in Ho. rewrite (MU3 x ltac:(cbn [outside]; clear - Ho; lia)). apply P2; [exact Hx | clear - Ho; lia | clear - Ho; lia]. }
  split.
  { apply (rw_cells_agree asegs m1 m3 _ _ BW1); [| exact (wmono_trans asegs _ _ _ WM2 WM3)]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU3 x ltac:(cbn [outside]; clear - Hx APIR; lia)). apply PRES2; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia] | clear - Hx APPI PL PH HRET; lia]. }
  split.
  { unfold readp_cells. replace (len - (off + ret)) with (blen - ret) by (subst blen; clear; lia). replace (D + (off + ret)) with (D + off + ret) by (clear; lia). exact RC3. }
  (* [comment removed for export] *)
  exists bs. split; [| split; [exact LF|]].
  - apply (bytes_at_agree asegs m1 m _ _ SRC1). intros x Hx. cbv beta in Hx. rewrite LF in Hx. symmetry. apply MU1. cbn [outside].
    pose proof (live_ne_apart RT AF Σ m D max BI 128 ART0 IND INBI ltac:(intros E; injection E; intros _; exact NDBI)) as APDI.
    clear - Hx APDI DLO HLO1 HOFF HLEN HRET. subst blen. split; [lia| split; [lia| exact I]].
  - apply (bytes_at_agree asegs m2 m3 _ _ OB2). intros x Hx. cbv beta in Hx. rewrite LF in Hx. apply MU3. cbn [outside]. clear - Hx APPR PL PH HRET. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Definition read_eof_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len fl OUT outl : Z) (rrw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 outl ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw (Z_to_bv 64 4294967295) padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D len rmaxw rflw) ->
  0 < OUT -> OUT + outl < 2 ^ 63 -> 0 < outl < 2 ^ 31 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_read m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(BI + 48, BI + 52)] m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16 + 9) rrw (Z_to_bv 64 4294967295) padw (Z_to_bv 64 BB)))).

Theorem read_eof_cps : read_eof_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len fl OUT outl rrw padw rmaxw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INR RAL RC OUT0 OUTHI HOUTL ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 96) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI. pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCBI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BB0 & BBLO' & _). assert (BBLO : BB + 16 <= lo) by (clear - BBLO' LOW; lia). clear BBLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BB 16 ART0 INBB ltac:(lia)) as BBHI. pose proof (proj2 (af_acc_live RT AF Σ m BB 16 ART0 INBB)) as ACCBB.
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (R0 & RLO' & _). assert (RLO : R + 32 <= lo) by (clear - RLO' LOW; lia). clear RLO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m R 32 ART0 INR ltac:(lia)) as RHI. pose proof (proj2 (af_acc_live RT AF Σ m R 32 ART0 INR)) as ACCR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  unfold readp_cells in RC. rewrite Z.sub_diag in RC.
  pose proof (rd_eof_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R OUT outl fl rrw padw (Z_to_bv 64 (D + len)) rmaxw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR OUT0 OUTHI HOUTL MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (x0 & x1 & x2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & BW1).
  fold usp in MU1, ST1. exists m1. split; [do 16 eexists; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 96) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  split; [| exact BW1].
  intros x Hx Ho. cbn [outside] in Ho. apply MU1. cbn [outside]. split; [clear - Ho; lia | split; [| exact I]].
  destruct (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia.
Qed.
End CRd.
