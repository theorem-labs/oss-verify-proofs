(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_lib2 RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_d1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma free_q1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (A n S lo : Z) (b1 : byte) (cid : word) (tr : list Z) (tj : list byte),
  leafc st m -> RTWF st -> mem_inv bsegs m -> tp = wz ATP ->
  a0 = wz A_ALLOC -> a1 = wz (A + -16) -> a2 = wz A -> a3 = wz S ->
  0 <= n < 2^40 -> AIMG_HI + 16 <= A -> A + 8 <= alloc_ceiling -> bv_unsigned sp <= S -> S + 16 <= 2^64 ->
  0 <= zlen tr < 2^32 ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (A + -16) [C1 (zb CHUNK_QUARANTINE); C1 b1; C2 (wz (size_hi n)); C4 (wz (size_lo n)); C8 cid] ->
  rw_cells bsegs m (st_t st) [C8 (wz (st_ctx st)); CB 72 tj] ->
  rw_cells bsegs m (st_ctx st + CTX_TID) [C4 (wz 0)] ->
  rw_cells bsegs m S [C8 (wz (S + 16)); C8 (wz (zlen tr))] ->
  evt bsegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x3610c) (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2' (wz (A + -16)) (wz S) (wz (S + 16)) (wz (zlen tr)) (wz (S + 16)) (wz (st_ctx st)) a4' a5' a6' a7'
                    (wz A_ALLOC) (wz 0) (wz (st_t st)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz ADEPOT_PUT) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - 48)
      /\ rw_cells bsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQCHUNK) fc None m (seg_rom bsegs)).
Proof.
  intros until tj. intros LC WF MI TP -> -> -> -> Hn A1 A2 HS1 HS2 TRL ST HCL LO HDR TT TID SO.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (size_hilo n Hn) as (SH1 & SL1 & SHL). pose proof (t_range st WF) as TR. olin TR.
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). pose proof (loose0_range st WF cb ck CL1) as (CR1 & CR2 & CR3 & CR4).
  unfold CHUNK_QUARANTINE, KHIGHMEM_BEG, AIMG_HI, AQCHUNK, ADEPOT_PUT, A_ALLOC, CTX_TID in *. idtac.
  leaf_prep. subst tp.
  carve_frame 48%nat ST.
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (sxb_zb_small' 3) by lia.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  assert (HWL : Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st \/ st_ctx st + 160 <= fst iv)) [(bv_unsigned sp - 64, bv_unsigned sp)]).
  { unfold AIMG_LO, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (leafc_keep st _ m mx MU WM HWL LC) as LC0 end.
  call get_current_thread_c; [exact LC0| exact WF| eassumption| reflexivity| rewrite ?unsigned_lit by lia; exact ST| idtac; lia| rewrite ?unsigned_lit by lia; lia|].
  cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end. restk. rewrite ?unsigned_lit in ST by lia.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (sx32_lit 0) by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma free_q2_spec :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (vra v0 v1 v2 v3 v4 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (A n S id : Z) (b1 : byte) (cid fw : word),
  mem_inv bsegs m ->
  a0 = wz id -> 0 <= id < 2^32 ->
  0 <= n < 2^40 -> AIMG_HI + 16 <= A -> A + 8 <= alloc_ceiling ->
  alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells bsegs m (A + -16) [C1 (zb CHUNK_QUARANTINE); C1 b1; C2 (wz (size_hi n)); C4 (wz (size_lo n)); C8 cid] ->
  rw_cells bsegs m A [C8 fw] ->
  rw_cells bsegs m (bv_unsigned sp) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0 t1 t2 v0 v1 (wz A_QUAR) (wz (qcache_t st)) (wz (acache st)) (wz S) (wz (A + -16)) (wz (usz n)) a6 a7
                    v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz AQPUT) fc None m' (seg_rom bsegs)
      /\ munch [(A, A + 8)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (A + -16) [C1 (zb CHUNK_QUARANTINE); C1 b1; C2 (wz (size_hi n)); C4 (wz (size_lo n)); C8 cid]
      /\ rw_cells bsegs m' A [C8 (wz id)]
      /\ rw_cells bsegs m' (bv_unsigned sp) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra])
    (MS (mkR (wz 0x3610c) sp gp tp t0 t1 t2 (wz (A + -16)) (wz S) a0 a1 a2 a3 a4 a5 a6 a7
             (wz A_ALLOC) (wz 0) (wz (st_t st)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3610c) fc None m (seg_rom bsegs)).
Proof.
  intros until fw. intros MI -> Hid Hn A1 A2 SP1 SP2 HDR UW FR.
  pose proof (munch_refl [(A, A + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (size_hilo n Hn) as (SH1 & SL1 & SHL).
  unfold CHUNK_QUARANTINE, KHIGHMEM_BEG, AIMG_HI, AQPUT, A_QUAR, A_ALLOC, qcache_t, acache, T_QCACHE, T_ACACHE in *. idtac.
  leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (Z.mod_small id 4294967296), Z.lor_0_l by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  rewrite size_join by lia.
  lstep. lstep. (* [comment removed for export] *)
  do 6 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  finish; eassumption.
Qed.


End CeilWrap.
