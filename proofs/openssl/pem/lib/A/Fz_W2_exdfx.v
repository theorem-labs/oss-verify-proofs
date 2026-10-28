(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_ukit Fz_env Th_mutex Fz_M_free Fz_T_lock Fz_W1_defs Fz_W3_iface Fz_W2_exdl Fz_W2_exd Fz_W2_exdx Fz_W2_exdf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.


Definition fx_x1_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
                 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 (Z_to_bv 64 f) s7 s8 s9 s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_fx_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 W7_RETIRED_NX)]
    /\ rw_cells asegs m' (f / 8 + 2147450880) nx_shadow_retired.

Lemma fx_x1_walk : forall ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pd : Z) (hj sj : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 208 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> 0xbc6000 <= f -> f + 256 <= lo -> (f + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  stk asegs m lo (bv_unsigned sp + -192 - pd) ->
  rw_cells asegs m f [CB 8 hj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 32 sj] -> mem_inv asegs m ->
  evt asegs (fx_x1_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 F fc f pd m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 (Z_to_bv 64 f) s7 s8 s9 s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_fx_mset) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP HLO HLOS SPH F0 FIMG FLO FSH ST1 HDR SB MI. unfold SITE_fx_mset in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 32 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ (f / 8 + 2147450880) [] 32 sj [] (repeat 1%nat 32)) in SB; [| reflexivity]. cbn [repeat mk_CB_cells app] in SB.
  destruct HP as [-> | ->].
  1: replace (SP + -192 - 0) with (SP + -192) in * by lia.
  2: replace (SP + -192 - 16) with (SP + -208) in * by lia.
  (* [comment removed for export] *)
  all: zstep.
  all: do 20 (zstep; lfix).
  all: zstep; zstep. all: zstep; lfix.
  all: zstep; if_cases KF; zify_cond KF; [exfalso; lia|].
  all: zstep; do 32 (zstep; lfix).
  all: subst SP.
  all: unfold fx_x1_post, SITE_fx_release, W7_RETIRED_NX, nx_shadow_retired; cbn [repeat map].
  all: try replace (bv_unsigned sp + -192 - 0) with (bv_unsigned sp + -192) by lia.
  all: try replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia.
  all: apply evt_done; cbv beta; do 2 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fx_x2_post (ra0 sp gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 e0 e1 (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma fx_x2_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd : Z) (lowj : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 208 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 256 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -192 - pd) ->
  rw_cells asegs m (bv_unsigned sp + -192 - pd) [CB (Z.to_nat (88 + pd)) lowj; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 ra0] ->
  ro_cells asegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (fx_x2_post ra0 sp gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_fx_release) fc None m (seg_rom asegs)).
Proof.
  intros until lowj. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 FR FLG FLB MI. unfold SITE_fx_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  destruct HP as [-> | ->].
  1: change (Z.to_nat (88 + 0)) with 88%nat in FR.
  2: change (Z.to_nat (88 + 16)) with 104%nat in FR.
  1: replace (SP + -192 - 0) with (SP + -192) in * by lia.
  2: replace (SP + -192 - 16) with (SP + -208) in * by lia.
  (* [comment removed for export] *)
  all: zstep; clear FLG; zstep; lfix; zstep; zstep.
  all: do 13 zstep.
  all: zstep.
  1: release_frame FR ST1 SP. 2: release_frame FR ST1 SP.
  all: zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold fx_x2_post; apply evt_done; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption| assumption].
Qed.
