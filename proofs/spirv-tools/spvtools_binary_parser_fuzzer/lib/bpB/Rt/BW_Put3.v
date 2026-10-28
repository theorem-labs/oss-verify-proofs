(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocKit BllocRep BllocWalkKit BsDepotInv BW_MallocBase BW_Put1 BW_Enqueue1 BW_Put2 BW_Drain BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Variables (sp ra0 s0v s1v s2v s3v s4v s5v : word).
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (T : list Z) (rest : list word) (jk : list byte).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.

  Ltac trp H MU WM tac := first [ eapply rw_cells_transport in H | eapply u64arr_transport in H ]; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].

  Section PutDrain.
    Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem).
    Variables (U size TH qcache : Z) (ng fg LG bg gsz gcnt : Z) (nt ft LT bt : Z) (qmax qmin : Z).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
    Hypothesis QCR : 0 <= qcache < 2^64. Hypothesis QGT : qcache < bt.
    Hypothesis NGR : 0 <= ng < 2^63 /\ 0 <= fg < 2^64 /\ 0 <= LG < 2^64 /\ 0 <= bg. Hypothesis NTR : 0 < nt < 2^63 /\ 0 <= ft < 2^64 /\ 0 <= LT < 2^64 /\ 0 <= bt.
    Hypothesis BR : bg + bt < 2^63. Hypothesis QR : 0 <= qmax < 2^64 /\ 0 <= qmin < 2^64.
    Hypothesis LGR : ng <> 0 -> AHI_LO <= LG /\ LG + 24 <= aceil /\ LG mod 8 = 0 /\ (LG + 24 <= TH + OT_TQ \/ TH + OT_TQ + 32 <= LG).
    Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2208).
    Hypothesis PFR : rw_cells asegs m (bv_unsigned sp + -2208) (put_frame sp s6 U TH).
    Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))].
    Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest).
    Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -72) [C8 sp].
    Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].
    Hypothesis QM : rw_cells asegs m (AINST + OI_QMUTEX) [C8 (wz 0)].
    Hypothesis GQ : rw_cells asegs m (AINST + OI_GQ) [C8 (wz ng); C8 (wz fg); C8 (wz LG); C8 (wz bg)].
    Hypothesis GL : ng <> 0 -> rw_cells asegs m LG [C8 (wz 0); C8 (wz gsz); C8 (wz gcnt)].
    Hypothesis TQ : rw_cells asegs m (TH + OT_TQ) [C8 (wz nt); C8 (wz ft); C8 (wz LT); C8 (wz bt)].
    Hypothesis QC : rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].

    Let ENTRY := MS (enq_regs sp gp tp s7 s8 s9 s10 s11 U size TH qcache t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x96a04) fc None m (seg_rom asegs).
    Let DMEM := drain_mem (Z_to_bv 64 (bv_unsigned sp + -2208)) m lo (TH + OT_TQ) ng fg LG bg gsz gcnt nt ft LT bt qmax qmin qcache.

    Theorem put_drain_norec : bg + bt <= qmax ->
      evt asegs (fun ms' => exists m', free_ret_post sp ra0 s0v s1v s2v s3v s4v s5v gp tp s6 s7 s8 s9 s10 s11 F fc lo m' ms'
                               /\ exists m1, DMEM m1 0 /\ munch [(lo, bv_unsigned sp + -2128)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m') ENTRY.
    Proof.
      intros LE. unfold ENTRY.
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
      assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil) by (clear - LO THR; destruct THR as [(T1 & T2 & T3)]; pose proof (akobj_env _ _ T1 ltac:(clear; lia)); lia).
      unfold enq_regs, put_frame, OT_TQ, OT_CACHE, wz in *.

      step. step. if_cases K; zify_cond K. 2: { exfalso. rewrite ?unsigned_lit in K by (clear - QCR QGT NTR BR NGR; lia). clear - K QGT. lia. } clear K.
      step. step. step. step. step.
      eapply evt_cut.
      { eapply drain_norec with (lo := lo) (C := TH + 80) (ng := ng) (fg := fg) (LG := LG) (bg := bg) (gsz := gsz) (gcnt := gcnt) (nt := nt) (ft := ft) (LT := LT) (bt := bt) (qmax := qmax) (qmin := qmin) (qcache := qcache).
        all: rewrite ?unsigned_lit by (clear - SPR HI LO ACEILB; lia).
        - exact MI. - exact ST. - exact LO. - clear - HI; lia. - clear - HI SPT LO ACEILB; lia.
        - destruct THR as [(T1 & T2 & T3)]. clear - T1 T2 T3. split; [eapply akobj_sub; [exact T1| lia| lia]|]. split; [lia|]. Z.div_mod_to_equations; lia.
        - exact NGR. - exact NTR. - exact BR. - exact QR. - exact LGR. - exact QM. - exact GQ. - exact GL. - exact TQ. - exact QC. - exact LE. }
      cbv beta. intros ms1 PO. destruct PO as (t0' & t1' & a1' & a4' & a5' & a6' & a7' & m1 & -> & DM).
      pose proof DM as (MU1 & WM1 & MI1 & ST1 & _). unfold drain_W, AINST, OI_QMUTEX, OI_GQ in MU1. rewrite ?unsigned_lit in MU1 by (clear - SPR HI LO ACEILB; lia). rewrite ?unsigned_lit in ST1 by (clear - SPR HI LO ACEILB; lia).
      assert (LGB : ng <> 0 -> 17594333495296 <= LG /\ LG + 24 <= aceil) by (intros NE; destruct (LGR NE) as (X1 & X2 & _); unfold AHI_LO in X1; clear - X1 X2; lia).

      assert (TR5 : rw_cells asegs m1 (bv_unsigned sp + -2208) (put_frame sp s6 U TH)
                    /\ rw_cells asegs m1 (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
                    /\ u64arr asegs m1 (bv_unsigned sp + -2128 + 16) (map wz T ++ rest)
                    /\ rw_cells asegs m1 (bv_unsigned sp + -72) [C8 sp]
                    /\ rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0]).
      {       destruct (Z.eqb_spec ng 0) as [NG0|NG1]; [clear LGB| specialize (LGB NG1)]; cbn [app] in MU1.
        1: trp PFR MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp PFR MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
        1: trp ESO MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp ESO MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
        1: trp TRB MU1 WM1 ltac:(rewrite length_app, length_map, LR; clear - BND SPR HI NR; try acb; lia). 2: trp TRB MU1 WM1 ltac:(rewrite length_app, length_map, LR; clear - BND SPR HI NR LGB; try acb; lia).
        1: trp TFB MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp TFB MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
        1: trp F4 MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp F4 MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
        all: (split; [exact PFR| split; [exact ESO| split; [exact TRB| split; [exact TFB| exact F4]]]]). }
      clear PFR ESO TRB TFB F4. destruct TR5 as (PFR & ESO & TRB & TFB & F4). unfold put_frame, wz in PFR, ESO, TRB.
      all: clear MI ST QM GQ GL TQ QC.

      all: replace (ret_pc (Z_to_bv 64 616764)) with (Z_to_bv 64 616764) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      all: do 8 step; step; step.
      all: release_frame PFR ST1 (bv_unsigned sp + -2128).
      all: step; do 7 step; step; step.
      all: apply evt_done; exists m1; split; [| exists m1; split; [exact DM| split; [apply munch_refl| split; [apply wmono_refl| exact MI1]]]].
      all: unfold free_ret_post; do 15 eexists; split; [reflexivity|]; eapply icpt_frame_release; eassumption.
    Qed.

    Definition put_drain_rec_post : machine_state -> Prop := fun ms' =>
      exists (t0' t1' a4' a5' a6' a7' : word) m1,
        ms' = MS (mkR (wz 0x9693c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0' t1' t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ)) (wz (AINST + OI_Q)) (wz qmin)
                      (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2128)) a4' a5' a6' a7'
                      (wz size) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x9430c) fc None m1 (seg_rom asegs)
        /\ DMEM m1 256
        /\ rw_cells asegs m1 (bv_unsigned sp + -2208) (put_frame sp s6 U TH)
        /\ rw_cells asegs m1 (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
        /\ u64arr asegs m1 (bv_unsigned sp + -2128 + 16) (map wz T ++ rest)
        /\ rw_cells asegs m1 (bv_unsigned sp + -72) [C8 sp]
        /\ rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

    Theorem put_drain_rec : qmax < bg + bt -> evt asegs put_drain_rec_post ENTRY.
    Proof.
      intros GT. unfold ENTRY.
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
      assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil) by (clear - LO THR; destruct THR as [(T1 & T2 & T3)]; pose proof (akobj_env _ _ T1 ltac:(clear; lia)); lia).
      unfold enq_regs, put_frame, OT_TQ, OT_CACHE, wz in *.
      step. step. if_cases K; zify_cond K. 2: { exfalso. rewrite ?unsigned_lit in K by (clear - QCR QGT NTR BR NGR; lia). clear - K QGT. lia. } clear K.
      step. step. step. step. step.
      eapply evt_cut.
      { eapply drain_rec with (lo := lo) (C := TH + 80) (ng := ng) (fg := fg) (LG := LG) (bg := bg) (gsz := gsz) (gcnt := gcnt) (nt := nt) (ft := ft) (LT := LT) (bt := bt) (qmax := qmax) (qmin := qmin) (qcache := qcache).
        all: rewrite ?unsigned_lit by (clear - SPR HI LO ACEILB; lia).
        - exact MI. - exact ST. - exact LO. - clear - HI; lia. - clear - HI SPT LO ACEILB; lia.
        - destruct THR as [(T1 & T2 & T3)]. clear - T1 T2 T3. split; [eapply akobj_sub; [exact T1| lia| lia]|]. split; [lia|]. Z.div_mod_to_equations; lia.
        - exact NGR. - exact NTR. - exact BR. - exact QR. - exact LGR. - exact QM. - exact GQ. - exact GL. - exact TQ. - exact QC. - exact GT. }
      cbv beta. intros ms1 PO. destruct PO as (t0' & t1' & a4' & a5' & a6' & a7' & m1 & -> & DM).
      pose proof DM as (MU1 & WM1 & MI1 & ST1 & _). unfold drain_W, AINST, OI_QMUTEX, OI_GQ in MU1. rewrite ?unsigned_lit in MU1 by (clear - SPR HI LO ACEILB; lia). rewrite ?unsigned_lit in ST1 by (clear - SPR HI LO ACEILB; lia).
      assert (LGB : ng <> 0 -> 17594333495296 <= LG /\ LG + 24 <= aceil) by (intros NE; destruct (LGR NE) as (X1 & X2 & _); unfold AHI_LO in X1; clear - X1 X2; lia).
      destruct (Z.eqb_spec ng 0) as [NG0|NG1]; [clear LGB| specialize (LGB NG1)]; cbn [app] in MU1.
      1: trp PFR MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp PFR MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
      1: trp ESO MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp ESO MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
      1: trp TRB MU1 WM1 ltac:(rewrite length_app, length_map, LR; clear - BND SPR HI NR; try acb; lia). 2: trp TRB MU1 WM1 ltac:(rewrite length_app, length_map, LR; clear - BND SPR HI NR LGB; try acb; lia).
      1: trp TFB MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp TFB MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
      1: trp F4 MU1 WM1 ltac:(clear - BND SPR HI; try acb; lia). 2: trp F4 MU1 WM1 ltac:(clear - BND SPR HI LGB; try acb; lia).
      all: apply evt_done; unfold put_drain_rec_post; unfold AINST, OI_Q, OT_TQ, OT_CACHE, put_frame, wz; do 7 eexists; split; [reflexivity|].
      all: split; [exact DM|]; split; [exact PFR|]; split; [exact ESO|]; split; [exact TRB|]; split; [exact TFB| exact F4].
    Qed.
  End PutDrain.
End HCW.
