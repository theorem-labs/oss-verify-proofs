(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_grow Fz_W1_write Fz_W1_read Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition GT_HEAD : Z := 0x3046a4.
Definition GT_JOIN : Z := 0x304700.
Definition SITE_gt_read : Z := 0x30470c.
Definition gt_frame (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma land32_small : forall x, 0 <= x < 2 ^ 32 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. Qed.
Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition gt_s0_post (sp gp tp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' : word) (BI BB R OUT size fl j doff lo : Z) (rrw numw padw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (jk : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x304644) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 OUT) (Z_to_bv 64 doff) (Z_to_bv 64 j) (Z_to_bv 64 1) (Z_to_bv 64 doff) (Z_to_bv 64 j) (Z_to_bv 64 10)
                 a6 a7 (Z_to_bv 64 BI) (Z_to_bv 64 size) (Z_to_bv 64 R) (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 GT_HEAD) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) (CB 8 jk :: gt_frame s5' s4' s3' s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)).

Local Ltac gt_s0_tail SP HJR HDO doff :=
  do 4 zstep; zstep; th_if_lit;                                     (* [comment removed for export] *)
  zstep; zstep; zstep; rewrite land32_small by (clear - HJR; lia);     (* [comment removed for export] *)
  zstep; zstep; zstep;                                               (* [comment removed for export] *)
  subst SP; rewrite ?Z_to_bv_bv_unsigned;
  unfold gt_s0_post, GT_HEAD, gt_frame, bio_w1_cells; apply evt_done; do 2 eexists; split; [reflexivity|];
  split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [eassumption|]; split; assumption.

Lemma gt_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R OUT size fl blen doff j : Z) (rrw numw padw rmw rflw : word),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m R [C8 (Z_to_bv 64 blen); C8 (Z_to_bv 64 doff); C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BI + 128 <= BB \/ BB + 16 <= BI) -> (BI + 128 <= R \/ R + 32 <= BI) ->
  0 < OUT -> 2 <= size < 2^31 -> 0 < blen < 2^31 - 1 -> 0 < doff < 2^63 -> j = Z.min blen (size - 1) -> mem_inv asegs m ->
  evt asegs (gt_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' BI BB R OUT size fl j doff lo rrw numw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 size) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_gets) fc None m (seg_rom asegs)).
Proof.
  intros until rflw. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR OUT0 HSZ HBL HDO HJ MI.
  unfold e_mem_gets, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (SP - 80, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  zstep. do 3 zstep. zstep. th_if_lit.                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  zstep. do 4 zstep. zstep. th_if_lit.                         (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. zstep. rewrite (fl_readp_sel fl) by lia.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -64). zstep. try th_ret_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  zstep. if_cases KI; zify_cond KI. 2:{ exfalso. rewrite ?unsigned_lit in KI by lia. lia. }
  zstep. if_cases Km; zify_cond Km; signed_lits_in Km.
  - rewrite (Z.min_l blen (size - 1)) in HJ by lia. assert (HJR : 1 <= j < 2 ^ 31 - 1) by (clear - HJ HBL; lia). subst j.
    zstep. rewrite sextw_small by lia. zstep. if_cases KZ; zify_cond KZ; signed_lits_in KZ. { exfalso. lia. }          (* [comment removed for export] *)
    gt_s0_tail SP HJR HDO doff.
  - rewrite (Z.min_r blen (size - 1)) in HJ by lia. assert (HJR : 1 <= j < 2 ^ 31 - 1) by (clear - HJ HSZ; lia). subst j.
    zstep. zstep. rewrite sextw_small by lia. zstep. if_cases KZ; zify_cond KZ; signed_lits_in KZ. { exfalso. lia. }                  (* [comment removed for export] *)
    replace (size + -1) with (size - 1) by (clear; lia). gt_s0_tail SP HJR HDO doff.
Qed.

(* [comment removed for export] *)
Definition gt_join_post (ra sp gp tp t2 s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (j : Z) (m : mem) (junk : list byte) (off : Z)
    : machine_state -> Prop :=
  fun ms => exists (k : Z) (x5 x6 x10 x13 x14 x16 x17 : word),
    ms = MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 (Z_to_bv 64 j) (Z_to_bv 64 k) x13 x14 (Z_to_bv 64 10) x16 x17 s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 GT_JOIN) fc None m (seg_rom asegs) /\ 1 <= k <= j
    /\ (k < j -> nth_error junk (Z.to_nat (off + k - 1)) = Some (Z_to_bv 8 10)).

Lemma gt_loop : forall (n : nat) ra sp gp tp t2 s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x5 x6 x16 x17 (F : bvmap 5 word) fc (m : mem) (D max doff off j i : Z) (junk : list byte),
  acc asegs m D max -> u8arr asegs m D junk -> Z.of_nat (length junk) = max -> 0 < D -> D + max < 2 ^ 63 ->
  doff = D + off -> 0 <= off -> 0 <= i -> i + Z.of_nat n + 1 = j -> off + j <= max -> j < 2 ^ 31 -> mem_inv asegs m ->
  evt asegs (gt_join_post ra sp gp tp t2 s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc j m junk off)
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 (doff + i)) (Z_to_bv 64 j) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (doff + i)) (Z_to_bv 64 (j - i)) (Z_to_bv 64 10) x16 x17
             s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GT_HEAD) fc None m (seg_rom asegs)).
Proof.
  induction n as [|n IH]; intros until junk; intros ACCD DU LJ D0 DMAX -> HOFF Hi Hn HJM HJ MI; unfold GT_HEAD.
  - chk_pass ACCD (D + off + i) 1 0x3046b4 16 17.
    destruct (nth_error junk (Z.to_nat (off + i))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (u8arr_read asegs _ D junk (off + i) b (Z_to_bv 64 (D + off + i)) DU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. cbv beta. zstep. if_cases Ke; zify_cond Ke.
    + apply evt_done. unfold gt_join_post, GT_JOIN. exists (i + 1). do 7 eexists. split; [reflexivity |]. split; [lia|].
      intros _. replace (off + (i + 1) - 1) with (off + i) by lia. rewrite Hb. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b). f_equal. rewrite ?unsigned_lit in Ke by lia. exact Ke.
    + zstep. zstep. zstep. zstep. replace (j - i + -1) with 0 by lia. zstep. th_if_lit. zstep. zstep.
      apply evt_done. unfold gt_join_post, GT_JOIN. exists j. do 7 eexists. split; [reflexivity |]. split; [lia| intros HK; exfalso; clear - HK; lia].
  - chk_pass ACCD (D + off + i) 1 0x3046b4 16 17.
    destruct (nth_error junk (Z.to_nat (off + i))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
    pose proof (u8arr_read asegs _ D junk (off + i) b (Z_to_bv 64 (D + off + i)) DU Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. cbv beta. zstep. if_cases Ke; zify_cond Ke.
    + apply evt_done. unfold gt_join_post, GT_JOIN. exists (i + 1). do 7 eexists. split; [reflexivity |]. split; [lia|].
      intros _. replace (off + (i + 1) - 1) with (off + i) by lia. rewrite Hb. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b). f_equal. rewrite ?unsigned_lit in Ke by lia. exact Ke.
    + zstep. zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz; try (exfalso; rewrite ?unsigned_lit in Kz by lia; lia).
      rewrite swrap32_small by lia. replace (D + off + i + 1) with (D + off + (i + 1)) by lia. replace (i + 2) with (i + 1 + 1) by lia. replace (j - i + -1) with (j - (i + 1)) by lia.
      apply (IH ra sp gp tp t2 s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ _ F fc m D max (D + off) off j (i + 1) junk ACCD DU LJ D0 DMAX eq_refl HOFF); first [exact MI | lia].
Qed.

(* [comment removed for export] *)
Lemma gt_s1_walk : forall sp gp tp t0 t1 t2 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x10 x13 x14 x15 x16 x17 (F : bvmap 5 word) fc (m : mem) (j k : Z),
  evt asegs (eq (MS (mkR (Z_to_bv 64 SITE_gt_read) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 s2 s1 (Z_to_bv 64 k) x13 x14 x15 x16 x17
                       s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_mem_read) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 0x304644) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 x10 (Z_to_bv 64 j) (Z_to_bv 64 k) x13 x14 x15 x16 x17
             s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 GT_JOIN) fc None m (seg_rom asegs)).
Proof.
  intros. unfold GT_JOIN. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  zstep. zstep. zstep. apply evt_done. unfold SITE_gt_read, e_mem_read. reflexivity.
Qed.

(* [comment removed for export] *)
Definition gt_s2_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (OUT k lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(OUT + k, OUT + k + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (OUT + k) [C1 (Z_to_bv 8 0)].

Lemma gt_s2_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (s2x s3x s4x : word)
    (F : bvmap 5 word) fc (m : mem) (lo OUT k P np : Z) (ob : byte) (jk : list byte),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -64) (CB 8 jk :: gt_frame s5' s4' s3' s2' s1' s0' ra0) ->
  acc asegs m P np -> 0 <= P -> P <= OUT -> OUT + k + 1 <= P + np -> P + np <= lo -> (P + np <= 0x7fff8000 \/ 0x10007fff8000 <= P) -> (P + np <= 0x10000 \/ 0xbc6000 <= P) ->
  rw_cells asegs m (OUT + k) [C1 ob] -> 0 < k < 2^31 -> 0 < OUT -> mem_inv asegs m ->
  evt asegs (gt_s2_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc OUT k lo m)
    (MS (mkR (Z_to_bv 64 SITE_gt_read) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 OUT) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
             s2x s3x s4x (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SITE_gt_read) fc None m (seg_rom asegs)).
Proof.
  intros until jk. intros HLO HLOS SPH ST UT FR ACCO P0 PL PH PLO PSH PUT OC HK OUT0 MI.
  unfold SITE_gt_read, gt_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(OUT + k, OUT + k + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(OUT + k, OUT + k + 1)]) by ut_fp_lia. assert (HWS : sh_fp [(OUT + k, OUT + k + 1)]) by sh_fp_lia.
  zstep. if_cases Kk; zify_cond Kk; try (rewrite ?signed_of_Z in Kk by (clear - HK; lia)); try (exfalso; clear - Kk HK; lia). all: try clear Kk.
  zstep. chk_pass ACCO (OUT + k) 1 0x304724 11 12.
  remember (OUT + k) as Pk eqn:EPk. zstep. th_fix_lit_store. subst Pk.
  do 7 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gt_s2_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition gt_e_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (BI BB OUT fl lo : Z) (rrw numw padw : word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(BI + 48, BI + 52); (OUT, OUT + 1); (bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)) /\ rw_cells asegs m' OUT [C1 (Z_to_bv 8 0)].

Lemma gt_e_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI BB BM R OUT size fl P np : Z) (rrw numw padw dw rmw rflw : word) (ob : byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] -> acc asegs m BB 16 -> 0 < BB -> BB mod 16 = 0 -> 0x10007fff8000 <= BB -> BB + 16 <= lo ->
  rw_cells asegs m R [C8 (Z_to_bv 64 0); C8 dw; C8 rmw; C8 rflw] -> acc asegs m R 32 -> 0 < R -> R mod 16 = 0 -> 0x10007fff8000 <= R -> R + 32 <= lo ->
  (BI + 128 <= BB \/ BB + 16 <= BI) -> (BI + 128 <= R \/ R + 32 <= BI) ->
  acc asegs m P np -> 0 <= P -> P <= OUT -> OUT + 1 <= P + np -> P + np <= lo -> (P + np <= 0x7fff8000 \/ 0x10007fff8000 <= P) -> (P + np <= 0x10000 \/ 0xbc6000 <= P) ->
  (P + np <= BI \/ BI + 128 <= P) -> rw_cells asegs m OUT [C1 ob] -> 1 <= size < 2^31 -> 0 < OUT -> mem_inv asegs m ->
  evt asegs (gt_e_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc BI BB OUT fl lo rrw numw padw m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 size) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_gets) fc None m (seg_rom asegs)).
Proof.
  intros until ob. intros HLO HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR ACCO P0 PL PH PLO PSH PUT API OC HSZ OUT0 MI.
  unfold e_mem_gets, g_shadow_memory_dynamic_address, bio_w1_cells in *. destruct FLOK as (FLR & FL512).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(BI + 48, BI + 52); (OUT, OUT + 1); (SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(BI + 48, BI + 52); (OUT, OUT + 1); (SP - 80, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(BI + 48, BI + 52); (OUT, OUT + 1); (SP - 80, SP)]) by sh_fp_lia.
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia). assert (BBAL8 : BB mod 8 = 0) by (clear - BBAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : R mod 8 = 0) by (clear - RAL; Z.div_mod_to_equations; lia).
  assert (EUBI : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 7 zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep.
  zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. zstep. rewrite (fl_readp_sel fl) by lia.
  zstep. do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. th_frame 16%nat [8; 8]%nat ST. zstep. th_fix_lit_store. zstep. zstep.
  zstep. zstep. zstep. do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small fl) by lia. zstep. zstep. rewrite ?(unsigned_lit fl) by lia. rewrite (and_clr15 fl) by lia. zstep.
  zstep. zstep. zstep. th_release FR0 (SP + -64). zstep. try th_ret_lit.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  zstep. th_if_lit.                                            (* [comment removed for export] *)
  zstep. if_cases Km; zify_cond Km; signed_lits_in Km. 2:{ exfalso. lia. }    (* [comment removed for export] *)
  zstep. zstep. th_if_lit.                                     (* [comment removed for export] *)
  chk_pass ACCO OUT 1 0x3046f4 10 11.
  zstep. zstep.
  remember (OUT + 0) as Pk eqn:EPk. zstep. th_fix_lit_store. subst Pk.
  do 7 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold gt_e_post, bio_w1_cells. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma clr15_idem : forall fl, fl - fl mod 16 - (fl - fl mod 16) mod 16 = fl - fl mod 16.
Proof. intros fl. Z.div_mod_to_equations. lia. Qed.

Section CGt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.

Definition GT_W (BI R OUT k : Z) : list (Z * Z) := [(BI + 48, BI + 52); (R, R + 24); (OUT, OUT + k + 1)].

(* [comment removed for export] *)
Definition gets_data_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl OUT size : Z) (rrw numw padw rmaxw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 size ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off < len -> len <= max -> max < 2 ^ 31 - 1 -> 2 <= size < 2 ^ 31 -> dst_blk (rt_live RT Σ) OUT size [BI; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_gets m)))
    (ASTA RT Σ PMc (fun ms => exists (k : Z) (rmaxw' : word) (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 k) m' ms
        /\ 1 <= k <= Z.min (len - off) (size - 1)
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GT_W BI R OUT k) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' R (readp_cells len D (off + k) rmaxw' rflw) /\ rw_cells asegs m' (OUT + k) [C1 (Z_to_bv 8 0)]
        /\ (exists bsr : list byte, bytes_at asegs m' OUT bsr /\ Z.of_nat (length bsr) = k
               /\ (k < Z.min (len - off) (size - 1) -> nth_error bsr (Z.to_nat (k - 1)) = Some (Z_to_bv 8 10))))).

Theorem gets_data_cps : gets_data_stmt.
Proof.
  pose proof (read_data_cps RT AF GOBJ AFP MCP) as C_RD.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl OUT size rrw numw padw rmaxw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INR RAL RC IND NDBI NDR HOFF HLEN HMAX HSZ DST ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64). set (blen := len - off) in *. set (j := Z.min blen (size - 1)) in *.
  assert (HJ : 1 <= j <= blen /\ j <= size - 1) by (subst j blen; clear - HOFF HSZ; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
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
  pose proof DST as (p & k0 & INP & PL & PH & PNE).
  assert (NPI : p <> BI) by (intros ->; apply PNE; left; reflexivity). assert (NPR : p <> R) by (intros ->; apply PNE; right; left; reflexivity).
  assert (NPD : p <> D) by (intros ->; apply PNE; do 2 right; left; reflexivity). clear PNE.
  pose proof (af_live_range RT AF Σ m p k0 ART0 INP) as (P0 & PLO' & PSEG). assert (PLO : p + k0 <= lo) by (clear - PLO' LOW; lia). clear PLO'.
  pose proof (proj1 (afp_live_mem RT GOBJ AFP Σ m p k0 ART0 INP ltac:(clear - PL PH HSZ; lia))) as PSH.
  pose proof (live_ne_apart RT AF Σ m p k0 BI 128 ART0 INP INBI ltac:(intros E; injection E; intros _; exact NPI)) as APPI.
  pose proof (live_ne_apart RT AF Σ m p k0 R 32 ART0 INP INR ltac:(intros E; injection E; intros _; exact NPR)) as APPR.
  assert (COP : lo + RT_STACK <= usp1 /\ usp1 + 16 <= USTACK_TOP /\ usp1 mod 16 = 0).
  { fold usp in SPA. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|]. split; [unfold USTACK_TOP in *; clear - NUM; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 4). lia. }
  pose proof RC as RC'. unfold readp_cells in RC.
  (* [comment removed for export] *)
  pose proof (gt_s0_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R OUT size fl blen (D + off) j rrw numw padw rmaxw rflw
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR
                ltac:(clear - P0 PL; lia) HSZ ltac:(clear - HOFF HLEN HMAX; subst blen; lia) ltac:(clear - D0 DLO HLO1 SPH HOFF HLEN; lia) eq_refl MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (jk & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & BW1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 80) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Hx; [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  assert (P1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> m1 x = m x).
  { intros x Hx HnF. apply MU1. cbn [outside]. split; [clear - HnF; lia | split; [| exact I]]. destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia. }
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; exact (conj ST1 (conj LOW COP))).
  destruct (live_CB RT AF Σ m1 D max ART1 IND ltac:(clear - HOFF HLEN; lia)) as (junk & LJ & DC1).
  (* [comment removed for export] *)
  pose proof (gt_loop (Z.to_nat (j - 1)) (Z_to_bv 64 0x304644) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t2 sp (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 size) (Z_to_bv 64 R)
                s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 t0 t1 a6 a7 F fc m1 D max (D + off) off j 0 junk (proj2 (af_acc_live RT AF Σ m1 D max ART1 IND)) (u8arr_of_rw_cells asegs m1 D _ junk DC1)
                ltac:(rewrite LJ; clear - HOFF HLEN; lia) ltac:(clear - D0; lia) ltac:(clear - DLO HLO1 SPH; lia) eq_refl ltac:(clear - HOFF; lia) ltac:(clear; lia)
                ltac:(rewrite Z2Nat.id by (clear - HJ; lia); clear; lia) ltac:(clear - HJ HLEN; subst blen; lia) ltac:(clear - HJ HSZ; lia) MI1) as WL.
  rewrite Z.add_0_r, Z.sub_0_r in WL. change (0 + 1) with 1 in WL.
  cl_lift WL Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (k & x5 & x6 & x10 & x13 & x14 & x16 & x17 & -> & HK & HLF) & Hc2'). clear Hc2.
  pose proof (gt_s1_walk sp gp (Z_to_bv 64 0xba3ef0) x5 x6 t2 (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 size) (Z_to_bv 64 R) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x10 x13 x14 (Z_to_bv 64 10) x16 x17 F fc m1 j k) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  apply (C_RD Σ PMc (Z_to_bv 64 SITE_gt_read) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) x5 x6 t2 sp (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 k) x13 x14 (Z_to_bv 64 10) x16 x17
           (Z_to_bv 64 BI) (Z_to_bv 64 size) (Z_to_bv 64 R) (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo BI BB BM R D len max off (fl - fl mod 16) OUT k
           rrw numw padw rmaxw rflw FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW1 (fl_ok_clr15 fl FLOK) INBB BBAL).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia] | clear - Hx APIB; lia]. }
  { exact INR. } { exact RAL. }
  { apply (rw_cells_agree asegs m m1 _ _ RC'); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply P1; [apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia] | clear - Hx APIR; lia]. }
  { exact IND. } { exact NDBI. } { exact NDR. } { exact HOFF. } { exact HLEN. } { clear - HMAX; lia. } { clear - HK HJ HSZ; lia. }
  { exists p, k0. split; [exact INP|]. split; [exact PL|]. split; [clear - PH HK HJ; lia|]. cbn [In]. clear - NPI NPR NPD. intuition. }
  { exact ART1. } { exact MI1. } { exact CO1. } { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (rmaxw2 & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BW2 & RC2 & (bsr & SRCb & LBSR & OBb)) & Hc4'). clear Hc4.
  destruct RS2 as (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (Z.min_r (len - off) k) in PRES2, RC2, Hc4' by (clear - HK HJ; subst blen; lia). rewrite clr15_idem in BW2.
  rewrite (ret_pc_even SITE_gt_read) in Hc4' by (unfold SITE_gt_read; lia).
  assert (P2 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 48 <= bv_unsigned x < BI + 52) -> outside (RD_W BI R OUT k) (bv_unsigned x) -> m2 x = m x).
  { intros x Hx HnF Ho. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) Ho). exact (P1 x Hx HnF). }
  assert (FR2 : rw_cells asegs m2 usp1 (CB 8 jk :: gt_frame s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold gt_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES2; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia | unfold RD_W; cbn [outside]; unfold usp1 in Hx; clear - Hx BILO RLO PLO PL PH HK HJ HLO1; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ m2 p k0 ART2 INP) as (WRP2 & ACCP2).
  destruct (wr_at_rw_C1 m2 (OUT + k) (wr_at_sub m2 p k0 (OUT + k) 1 WRP2 ltac:(clear - PL HK; lia) ltac:(clear - PH HK HJ; lia) ltac:(clear; lia))) as (ob & OC2).
  (* [comment removed for export] *)
  pose proof (gt_s2_walk ra sp gp y0 y1 y2 s0 s1 h1 h2 h3 h4 h5 h6 h7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 (Z_to_bv 64 BI) (Z_to_bv 64 size) (Z_to_bv 64 R) F2 fc2 m2 lo OUT k p k0 ob jk
                ltac:(clear - HLO1; lia) HLOS SPH ST2 UT2 FR2 ACCP2 ltac:(clear - P0; lia) PL ltac:(clear - PH HK HJ; lia) PLO PSH PSEG OC2 ltac:(clear - HK HJ HSZ; lia) ltac:(clear - P0 PL; lia) MI2) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  apply Hk. eapply ASTA_conseq; [exact Hc5|]. intros ms (z0 & z1 & z2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & z3 & z4 & z5 & z6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & OC3).
  fold usp in ST3. exists k, rmaxw2, m3. split; [do 16 eexists; reflexivity|]. split; [clear - HK HJ; subst j blen; lia|].
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ p k0); [exact INP | clear - Hin PL PH HK HJ; lia]. }
  split; [exact (conj ART3 (conj MI3 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) ST3)))|].
  split.
  { intros x Hx Ho. unfold GT_W in Ho. cbn [outside] in Ho. rewrite (MU3 x ltac:(cbn [outside]; split; [clear - Ho HK; lia | exact I])). apply P2; [exact Hx | clear - Ho; lia | unfold RD_W; cbn [outside]; clear - Ho; lia]. }
  split.
  { apply (rw_cells_agree asegs m2 m3 _ _ BW2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply MU3. cbn [outside]. split; [clear - Hx APPI PL PH HK HJ; lia | exact I]. }
  split.
  { apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply MU3. cbn [outside]. split; [clear - Hx APPR PL PH HK HJ; lia | exact I]. }
  split; [exact OC3|].
  (* [comment removed for export] *)
  rewrite (Z.min_r (len - off) k) in LBSR by (clear - HK HJ; subst blen; lia).
  exists bsr. split; [| split; [exact LBSR|]].
  - apply (bytes_at_agree asegs m2 m3 _ _ OBb). intros x Hx. cbv beta in Hx. rewrite LBSR in Hx. apply MU3. cbn [outside]. split; [clear - Hx; lia | exact I].
  - intros HKJ. fold blen in HKJ. fold j in HKJ.
    destruct SRCb as (SB0 & SB1 & SBI). pose proof (rw_cells_bytes_at asegs m1 D _ DC1) as DB1. cbn [cells_bytes cbytes] in DB1. rewrite app_nil_r in DB1. destruct DB1 as (DB0 & DBH & DBI).
    assert (L1 : (Z.to_nat (k - 1) < length bsr)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (clear - HK; lia); rewrite LBSR; clear - HK; lia).
    assert (L2 : (Z.to_nat (off + k - 1) < length junk)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by (clear - HK HOFF; lia); rewrite LJ; clear - HK HJ HOFF HLEN; subst j blen; lia).
    rewrite <- (SBI _ L1). rewrite <- (HLF HKJ). rewrite <- (DBI _ L2). rewrite !Z2Nat.id by (clear - HK HOFF; lia). f_equal. unfold wa. f_equal. clear. lia.
Qed.

(* [comment removed for export] *)
Definition gets_empty_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R OUT size fl : Z) (rrw numw padw dw rmw rflw : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 size ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R [C8 (Z_to_bv 64 0); C8 dw; C8 rmw; C8 rflw] ->
  1 <= size < 2 ^ 31 -> dst_blk (rt_live RT Σ) OUT 1 [BI] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_gets m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(BI + 48, BI + 52); (OUT, OUT + 1)] m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)) /\ rw_cells asegs m' OUT [C1 (Z_to_bv 8 0)])).

Theorem gets_empty_cps : gets_empty_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R OUT size fl rrw numw padw dw rmw rflw
    FDO MST -> -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INR RAL RC HSZ DST ART0 MI0 CALL HSTK.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 80 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
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
  destruct DST as (p & k0 & INP & PL & PH & PNE). assert (NPI : p <> BI) by (intros ->; apply PNE; left; reflexivity). clear PNE.
  pose proof (af_live_range RT AF Σ m p k0 ART0 INP) as (P0 & PLO' & PSEG). assert (PLO : p + k0 <= lo) by (clear - PLO' LOW; lia). clear PLO'.
  pose proof (proj1 (afp_live_mem RT GOBJ AFP Σ m p k0 ART0 INP ltac:(clear - PL PH; lia))) as PSH.
  pose proof (live_ne_apart RT AF Σ m p k0 BI 128 ART0 INP INBI ltac:(intros E; injection E; intros _; exact NPI)) as APPI.
  pose proof (af_acc_live RT AF Σ m p k0 ART0 INP) as (WRP & ACCP).
  destruct (wr_at_rw_C1 m OUT (wr_at_sub m p k0 OUT 1 WRP PL PH ltac:(clear; lia))) as (ob & OC).
  pose proof (gt_e_walk ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R OUT size fl p k0 rrw numw padw dw rmw rflw ob
                HLO1 HLOS SPH ST UT SHC BW FLOK ACCBI BI0 BIAL BIHI BILO BBC ACCBB BB0 BBAL BBHI BBLO RC ACCR R0 RAL RHI RLO APIB APIR
                ACCP ltac:(clear - P0; lia) PL PH PLO PSH PSEG APPI OC HSZ ltac:(clear - P0 PL; lia) MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  apply Hk. eapply ASTA_conseq; [exact Hc1|]. intros ms (x0 & x1 & x2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x4 & x5 & x6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & BW1 & OC1).
  fold usp in MU1, ST1. exists m1. split; [do 16 eexists; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 80) ART0 ltac:(clear - NUM; lia)); [| exact WM1].
    intros x Hx. apply MU1. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Hx;
      [apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia] | apply (acl_live _ _ _ p k0); [exact INP | clear - Hin PL PH; lia] | left; unfold USTACK_TOP in *; clear - Hin NUM; lia]. }
  split; [exact (conj ART1 (conj MI1 (conj WM1 ST1)))|].
  split; [| exact (conj BW1 OC1)].
  intros x Hx Ho. cbn [outside] in Ho. apply MU1. cbn [outside]. split; [clear - Ho; lia | split; [clear - Ho; lia | split; [| exact I]]].
  destruct (cl_split RT AF Σ m usp 80 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx); clear - H; lia.
Qed.
End CGt.
