(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_free Fz_W5_gsi Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Definition e_eclear : Z := 0x1f9330.        (* [comment removed for export] *)
Definition e_err_clear : Z := 0x1f8b04.     (* [comment removed for export] *)
Definition ECL_LOOP : Z := 0x1f9374.        (* [comment removed for export] *)
Definition ECL_DONE : Z := 0x1f938c.        (* [comment removed for export] *)
Definition SITE_ecl_egsi : Z := 0x1f9364.   (* [comment removed for export] *)
Definition SITE_ecl_call : Z := 0x1f9384.   (* [comment removed for export] *)
Definition SITE_ecr_free1 : Z := 0x1f8d0c.  (* [comment removed for export] *)
Definition SITE_ecr_free2 : Z := 0x1f8d4c.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ECL_LNW : word := Z_to_bv 64 (-1).
(* [comment removed for export] *)
Definition ecl_W (E i : Z) : list (Z * Z) :=
  [(E + 4 * i, E + 4 * i + 4); (E + 4 * i + 64, E + 4 * i + 68); (E + 8 * i + 128, E + 8 * i + 136); (E + 8 * i + 256, E + 8 * i + 264);
   (E + 8 * i + 384, E + 8 * i + 392); (E + 4 * i + 512, E + 4 * i + 516); (E + 8 * i + 576, E + 8 * i + 584); (E + 4 * i + 704, E + 4 * i + 708);
   (E + 8 * i + 768, E + 8 * i + 776)].
(* [comment removed for export] *)
Definition ECL_SITES : list (Z * Z) := [(SITE_ecl_call, e_eclear); (SITE_ecr_free1, e_err_clear); (SITE_ecr_free2, e_err_clear)].
Definition ECL_CALLS : list (Z * Z) :=
  [(SITE_ecl_call, e_err_clear); (SITE_ecr_free1, e_CRYPTO_free); (SITE_ecr_free1, e_free); (SITE_ecr_free2, e_CRYPTO_free); (SITE_ecr_free2, e_free)].

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition ecl_w0_post (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s3e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_state) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3e; C8 s2; C8 s1; C8 s0e; C8 rae]
    /\ stk bsegs m' lo (bv_unsigned sp + -48).

Lemma ecl_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 48 -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> mem_inv bsegs m ->
  evt bsegs (ecl_w0_post sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s3 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_eclear) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST HLOS HLO SPH UT SHC MI. unfold e_eclear. unfold g_shadow_memory_dynamic_address, SHB in SHC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  carve_frame 48%nat ST.
  do 7 zstep.
  do 6 zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned. rewrite ?Z_to_bv_bv_unsigned in FR.
  unfold ecl_w0_post, SITE_ecl_egsi, e_get_state, SHB. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| assumption].
Qed.

(* [comment removed for export] *)
Lemma ecl_w1 : forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (E : Z),
  0x10007fff8000 <= E -> E + 904 <= 2^47 -> img_untouched m ->
  evt bsegs (eq (MS (mkR (Z_to_bv 64 SITE_ecl_egsi) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 0) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ECL_LOOP) fc None m (seg_rom bsegs)))
    (MS (mkR (Z_to_bv 64 SITE_ecl_egsi) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ecl_egsi) fc None m (seg_rom bsegs)).
Proof.
  intros until E. intros EH ET UT. unfold SITE_ecl_egsi, ECL_LOOP.
  assert (EU1 : bv_unsigned (Z_to_bv 64 E) = E) by (apply unsigned_lit; lia).
  ths. if_false. do 3 ths.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ecl_wcall : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
    (F : bvmap 5 word) fc (m : mem) (E i : Z),
  img_untouched m ->
  evt bsegs (eq (MS (mkR (Z_to_bv 64 SITE_ecl_call) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 i) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                        (Z_to_bv 64 i) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 e_err_clear) fc None m (seg_rom bsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ECL_LOOP) fc None m (seg_rom bsegs)).
Proof.
  intros until i. intros UT. unfold ECL_LOOP, SITE_ecl_call, e_err_clear.
  do 4 ths.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ecl_next (i : Z) : Z := if i =? 15 then ECL_DONE else ECL_LOOP.
Lemma ecl_wnext : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
    (F : bvmap 5 word) fc (m : mem) (E i : Z),
  0 <= i < 16 -> img_untouched m ->
  evt bsegs (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (i + 1)) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (ecl_next i)) fc None m (seg_rom bsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 i) s3 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ecl_call) fc None m (seg_rom bsegs)).
Proof.
  intros until i. intros HI UT. unfold SITE_ecl_call.
  ths. ths.
  destruct (Z.eq_dec i 15) as [-> | NE].
  - unfold ecl_next, ECL_DONE, ECL_LOOP. cbn [Z.eqb Pos.eqb Z.add Pos.add Pos.succ]. if_false. apply evt_done. reflexivity.
  - unfold ecl_next, ECL_DONE, ECL_LOOP. replace (i =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite bv_eqb_Z, (unsigned_lit (i + 1)), (unsigned_lit 16) by lia.
    replace (i + 1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ecl_wz_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s1e s2e s3e s4e : word) (F : bvmap 5 word) (fc : bv 32)
    (lo E : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (m' : mem),
    ms = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 (E + 896)) a1' a2' a3 a4 a5 a6 a7 s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc rae) fc None m' (seg_rom bsegs)
    /\ munch [(E + 896, E + 904)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (E + 896) [C4 z64; C4 z64] /\ stk bsegs m' lo (bv_unsigned sp).

Lemma ecl_wz : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (rae s0e s1e s2e s3e s4e : word)
    (F : bvmap 5 word) fc (m : mem) (lo E : Z) (tp0 bt0 : word),
  0x10007fff8000 <= E -> E + 904 <= lo -> E mod 8 = 0 ->
  stk bsegs m lo (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp + -48 -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> acc bsegs m E 904 ->
  rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  rw_cells bsegs m (E + 896) [C4 tp0; C4 bt0] ->
  mem_inv bsegs m ->
  evt bsegs (ecl_wz_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rae s0e s1e s2e s3e s4e F fc lo E m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ECL_DONE) fc None m (seg_rom bsegs)).
Proof.
  intros until bt0. intros EH ET E8 ST HLOS HLO SPH UT ACC FR TB MI. unfold ECL_DONE, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(E + 896, E + 904)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HW : sh_fp [(E + 896, E + 904)]) by sh_fp_lia.
  assert (EU1 : bv_unsigned (Z_to_bv 64 E) = E) by (apply unsigned_lit; lia).
  zstep. zstep. ubs_if.
  ths. ths. rewrite unsigned_lit by lia. ths. ths. ths. if_false. ths.
  ths. ths. rewrite unsigned_lit by lia. ths. ths. ths. if_false. ths.
  do 6 ths. release_frame FR ST SP. ths. ths.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ecl_wz_post. apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.
