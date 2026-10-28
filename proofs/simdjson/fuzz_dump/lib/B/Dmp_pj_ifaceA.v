(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_defsA Pj_defsA Pj_os_defsA El_os_defsA El_ins_ifaceA El_defsA Dmp_hdefsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition pj_costE (i j : Z) : Z := DMP_PJ_CW * (j - i) - 2.
Lemma pj_needA_S : forall d, pj_needA (S d) = pj_needA d + DMP_PJ_FRAME_A.
Proof. intros d. unfold pj_needA. rewrite Nat2Z.inj_succ. lia. Qed.
Lemma pj_needA_0 : forall d, DMP_PJ_FRAME_A + DMP_PJ_LEAF_A <= pj_needA d.
Proof. intros d. unfold pj_needA, DMP_PJ_FRAME_A, DMP_PJ_LEAF_A. lia. Qed.

Definition pj_WA (OS : Z) : list (Z * Z) := [(OS, OS + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)].

Definition OSXF (m : mem) (OS : Z) : Prop := exists fill, OSX m OS fill /\ FILLOK fill.
Lemma FILLOK_after : forall f, FILLOK f -> FILLOK (fill_after f).
Proof. intros f H. unfold fill_after. destruct (Z.eqb_spec f 0xffffffff); [right; left; reflexivity| exact H]. Qed.
Lemma OSXF_after : forall m OS fill, OSX m OS (fill_after fill) -> FILLOK fill -> OSXF m OS.
Proof. intros m OS fill H F. exists (fill_after fill). split; [exact H| apply FILLOK_after; exact F]. Qed.

Lemma OSXF_of_fresh : forall m OS, OSFRESHA m OS -> OSXF m OS.
Proof. intros m OS H. exists 0xffffffff. split; [exact (OSFRESHA_OSX m OS H)| left; reflexivity]. Qed.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition pj_cpsA (d : nat) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : aenvA) (OS q fO : Z) (kO : nat) (i j : Z)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->

  aenvA_ok E -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E ->
  a_live RT Σ E -> AINV_A E m ->

  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  (ae_DOC E + 16 <= OS \/ OS + 288 <= ae_DOC E) ->
  OSXF m OS -> os_hullA m OS -> LOCBA m -> el_tploc m -> io_ssp m -> frm0 fc ->

  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + pj_needA d <= q -> q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + Z.of_nat d + 3 <= FRAMES_TOT -> pj_costE i j <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
     OSXF m' OS -> os_hullA m' OS -> LOCBA m' -> el_tploc m' -> frm0 fc' -> AINV_A E m' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - pj_costE i j <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q (pj_WA OS) m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz (ae_DOC E)) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_A) fc None m (seg_rom bsegs)).

Definition pj_root_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : aenvA) (OS q fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  aenvA_ok E -> a_live RT Σ E -> AINV_A E m ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  (ae_DOC E + 16 <= OS \/ OS + 288 <= ae_DOC E) ->
  OSFRESHA m OS -> bytes_at bsegs m (shad OS) (repeat z8 36) -> LOCBA m -> el_tploc m -> io_ssp m -> frm0 fc ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + pj_needA TAPE_MAX_DEPTH <= q -> q + 16 <= USTACK_TOP -> q mod 32 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 1027 <= FRAMES_TOT -> DMP_PJ_C0 + DMP_PJ_CW * ae_n E <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
     OSXF m' OS -> os_hullA m' OS -> LOCBA m' -> el_tploc m' -> frm0 fc' -> AINV_A E m' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - (DMP_PJ_C0 + DMP_PJ_CW * ae_n E) <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q (pj_WA OS) m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz (ae_DOC E)) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_A) fc None m (seg_rom bsegs)).

Lemma pj_root_ofA : pj_cpsA TAPE_MAX_DEPTH -> pj_root_cpsA.
Proof.
  intros PJ. unfold pj_root_cpsA. intros until m.
  intros FDO MST EOK AL AI INF FLO FHI O16 DJ FR SHO LB TPL IOS FRM HA MI ST NEED QT Q32 FRB CRB HK.
  pose proof (ok_wf E EOK) as WF. pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR].
  assert (HULL : os_hullA m OS) by (split; [exact (OSFRESHA_hull m OS FR)| exact SHO]).
  pose proof (OSXF_of_fresh m OS FR) as OXF.
  assert (FRB' : Z.of_nat (length (rt_frames RT Σ)) + Z.of_nat TAPE_MAX_DEPTH + 3 <= FRAMES_TOT) by (change (Z.of_nat TAPE_MAX_DEPTH) with 1024; lia).
  assert (CRB' : pj_costE 1 (ae_n E - 1) <= rt_credit RT Σ) by (unfold pj_costE, DMP_PJ_CW, DMP_PJ_C0 in *; lia).
  eapply (PJ Σ K E OS q fO kO 1 (ae_n E - 1)); try eassumption; try lia.
  intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HU' LB' TP' FRM' AI' LV FRS SP0 CR' PR.
  eapply HK; try eassumption. unfold pj_costE, DMP_PJ_CW, DMP_PJ_C0 in *. lia.
Qed.

End Stmts.
