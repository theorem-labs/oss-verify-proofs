(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Gm_iface Gq_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma amo_dec_bytes : forall rc, 1 <= rc < 2^31 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) (Z_to_bv 32 4294967295)))
  = le4 (Z_to_bv 64 (rc - 1)).
Proof.
  intros rc H. unfold amo_val. unfold le4 at 2. f_equal.
  rewrite bv_add_unsigned.
  assert (E : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) = rc).
  { pose proof (zext_extract_le4 (Z_to_bv 64 rc)) as Z. apply (f_equal bv_unsigned) in Z.
    unfold zext in Z. rewrite bv_zero_extend_unsigned in Z by (cbv; discriminate). rewrite Z. unfold zx32. rewrite !unsigned_lit by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite (Z.mod_small 4294967295) by lia.
  replace (rc + 4294967295) with ((rc - 1) + 1 * 4294967296) by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (rc - 1) 4294967296) by lia. symmetry. apply Z.mod_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.
(* [comment removed for export] *)
Lemma rc_bne_taken : forall rc, 2 <= rc < 2^31 -> negb (bv_eqb (sx32 (Z_to_bv 64 rc)) (Z_to_bv 64 1)) = true.
Proof.
  intros rc H. rewrite sx32_small by lia. rewrite bv_eqb_Z. rewrite !unsigned_lit by lia.
  apply Bool.negb_true_iff. apply Z.eqb_neq. lia.
Qed.

Section RC_DEFS.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition pixDestroy_rc_case (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (rc : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL RT (rt_live RT Σ) Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj_rc (rt_live RT Σ) m pix v cv rc -> 2 <= rc < 2^31 -> (pp + 8 <= pix \/ pix + 64 <= pp) ->
  lenv RT Σ m sp lo (LSTK 4) -> lres RT Σ 1 0 1 ->
  bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(pp, pp + 8); (pix + 20, pix + 24)] m m'
          /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' pix (pix_cells_rc v (rc - 1))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

Lemma pixDestroy_rc_of_cases : pixDestroy_rc_case 0 -> pixDestroy_rc_case 16 -> pixDestroy_rc_cps RT.
Proof.
  intros C0 C16. unfold pixDestroy_rc_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp pix v cv rc
    FDO MST TP A0 OP PPC POBJ RCB PPX ENV RES.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct ENV as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). Z.div_mod_to_equations; lia. }
  destruct AL as [AL|AL]; [eapply C0| eapply C16]; eassumption.
Qed.
End RC_DEFS.
