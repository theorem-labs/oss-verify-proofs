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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_objkit Gm_iface Gq_iface Gq_destroy_rc_defs LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma amo_inc_bytes : forall rc, 0 <= rc < 2^31 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) (Z_to_bv 32 1)))
  = le4 (Z_to_bv 64 (rc + 1)).
Proof.
  intros rc H. unfold amo_val. unfold le4 at 2. f_equal.
  rewrite bv_add_unsigned.
  assert (E : bv_unsigned (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) = rc).
  { pose proof (zext_extract_le4 (Z_to_bv 64 rc)) as Z. apply (f_equal bv_unsigned) in Z.
    unfold zext in Z. rewrite bv_zero_extend_unsigned in Z by (cbv; discriminate). rewrite Z. unfold zx32. rewrite !unsigned_lit by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite (Z.mod_small 1) by lia.
  rewrite (Z.mod_small (rc + 1) 4294967296) by lia. symmetry. apply Z.mod_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.

(* [comment removed for export] *)
Definition pixClone_post (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo pix : Z) (v : pixv) (rc : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a3' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pix) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp - 16, usp); (pix + 20, pix + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ rw_cells asegs m' pix (pix_cells_rc v (rc + 1)).

Lemma pixClone_evt : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp lo : Z) (pix : Z) (v : pixv) (rc : Z),
  rw_cells asegs m pix (pix_cells_rc v rc) -> acc asegs m pix 64 -> 0 <= rc < 2^31 - 1 -> 0 < pix -> pix mod 16 = 0 ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo usp -> lo <= usp - 16 -> usp <= 2^47 -> 0x10007fff8000 <= lo -> pix + 64 <= lo ->
  (pix + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= pix) -> (pix + 64 <= 0x10000 \/ SEGTOP_A <= pix) ->
  mem_inv asegs m ->
  evt asegs (pixClone_post ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m usp lo pix v rc)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pix) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_pixClone) fc None m (seg_rom asegs)).
Proof.
  intros until rc. intros PXC ACC RCB PX0 PX16 G1 G2 ST LO UHI LOH NLO NSH NSEG MI.
  unfold pix_cells_rc in PXC.
  unfold e_pixClone, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(usp - 16, usp); (pix + 20, pix + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x95b94; 0x95b4c; 0x95ba4].      (* [comment removed for export] *)
  idtac "MARK at amoadd".
  assert (AMO : amo_aligned AW (Z_to_bv 64 (pix + 20)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. clear - PX16. Z.div_mod_to_equations; lia. }
  amo_step AMO.
  rewrite (amo_inc_bytes rc ltac:(lia)).
  mem_after_store.
  idtac "MARK stored".
  lwalk (@nil Z).
  apply evt_done. unfold pixClone_post. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. unfold pix_cells_rc. exact PXC.
Qed.
