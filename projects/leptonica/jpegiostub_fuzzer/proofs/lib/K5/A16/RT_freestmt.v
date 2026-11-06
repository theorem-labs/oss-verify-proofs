(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import Exec RzCPS.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import RT_iface.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import R_sizeclass.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.A16 Require Import R_cache_defs R_prim_defs R_glue_defs R_depot_defs R_fs_defs R_thread R_qput RT_state RT_rep RT_freestate.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition quar_wfx (Σ : rtsA) : Prop :=
  qbytes (ql Σ) <= QMAX_L + 2 ^ 27 + 0x20000 /\ qbytes (qg Σ) <= QMAX_G + 0x10000
  /\ Forall (fun b => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ)
  /\ NoDup (map fst (ql Σ ++ qg Σ))
  /\ Forall (fun b => (length (snd b) <= 1021)%nat) (ql Σ ++ qg Σ)
  /\ Forall (qent_ok Σ) (qents Σ) /\ NoDup (map fst (qents Σ))
  /\ (forall c i, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some CkBatch ->
        c = 24 /\ In (p_abeg (l_SB (lay Σ)) 24 i) (map fst (ql Σ ++ qg Σ))).

(* [comment removed for export] *)
Definition rt_wfx (Σ : rtsA) : Prop :=
  layout_ok (lay Σ) /\ regs_wf Σ /\ live_wf Σ /\ sec_wf Σ /\ quar_wfx Σ /\ fs_wf Σ /\ budget_wf Σ
  /\ depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ))
  /\ d_n (dep Σ) + 2 < 2 ^ 16 /\ d_tot (dep Σ) + 255 < 2 ^ 20 /\ dep_inv (dep Σ).

(* [comment removed for export] *)
Definition drain_stmt : Prop :=
  forall (Σ : rtsA) (PMc : Model -> Prop) (ra0 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp : Z) (w0 w1 w2 w3 w4 w5 s6 : word),
  fdfs_only PMc -> mat_stable PMc ->
  ARTc Σ m -> rt_wfx Σ -> rt_count Σ -> 0x100000 < qbytes (ql Σ) ->
  qput_frame m (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x5dcd0) w0 w1 w2 w3 w4 w5 s6 ->
  stk asegs m lo (usp + -2208) -> l_ACEIL (lay Σ) <= lo -> lo + 0x4000 <= usp + -2208 -> usp <= 2 ^ 47 ->
  mem_inv asegs m ->
  cps asegs
    (ASTA RTA Σ PMc (eq (MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR)
                                 (Z_to_bv 64 (l_T (lay Σ) + 80)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x100000)
                                 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40650) fc None m (seg_rom asegs))))
    (fun cf => exists Σ' : rtsA,
       ASTA RTA Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
                                         (fc' : bv 32) (m' : mem),
           ms = MS (mkR (Z_to_bv 64 0x5dcd0) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0' t1' t2' w0 w1 a0' a1' a2' a3' a4' a5'
                        a6' a7' w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0x5dcd0) fc' None m' (seg_rom asegs)
           /\ ART_A Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -2128)   (* [comment removed for export] *)
           /\ rt_pres (live Σ) (frames Σ) (usp + -2128) m m') cf
       /\ live Σ' = live Σ /\ frames Σ' = frames Σ /\ lay Σ' = lay Σ /\ credit Σ' = credit Σ).
