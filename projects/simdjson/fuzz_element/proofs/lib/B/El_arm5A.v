(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface5 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
     Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_fzwA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_kitA Atp_h_defsA Atp_pidiA Atp_pdtorA Atp_h_gstrA
     Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_parsekA El_armkitA El_armkit2A El_gstrA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section Arm5.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.

Local Ltac ul := unfold GSTR_STACK_A, FUZZ_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac arm_gstr a :=
  intros W Σ K X E sel idx jr jos t ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 F fc m
    FDO MST LK OKE LE WFS SEL IDX AL FRS LPA LVB CRB ARTg MIg STg NEED AM FRM XD AUX SPB POST;
  pose proof LK as [(SPR & SPA') (SPT & SPA) (LLO & LOR) (FPOS & F64 & FSEG & FLO) (FSELF & SHB0 & SHT)];
  destruct X as [usp sp' f lo]; cbn [lf_usp lf_S1 lf_F lf_lo] in *;
  destruct LE as (EDOC & EFD & EKD & ELO & EHI); cbn [lf_usp lf_S1 lf_F lf_lo] in EDOC, EFD, EKD, ELO, EHI;
  pose proof AM as (C16 & C100 & C128 & CE & CO & CS & AI & LIB & NL & IOS); cbn [lf_usp lf_S1 lf_F lf_lo] in C16, C100, C128, CE, CO, CS;
  unfold lf_st; cbn [lf_usp lf_S1 lf_F lf_lo el_arm_pcA Z.leb Z.ltb andb nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add EL_ARMS_A];
  let NEED' := fresh "NEED'" in
  assert (NEED' : lo + 1024 + RT_STACK <= sp') by (clear - NEED; unfold arm_needA in NEED; cbn [Z.eqb Pos.eqb orb] in NEED; unfold RT_STACK in *; lia);
  let SLO := fresh "SLO" in assert (SLO : shad f + 128 <= sp' - 96) by (clear - SHT LOR SPR; ul);
  let FPW := fresh "FPW" in
  assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) (gstr_W sp' (sp' + 128))) by (intros Σx; unfold gstr_W; apply (fp_client_stack2 RT E Σx); rewrite ?ELO; clear - LOR SPR SPT; ul);
  let ARTM := fresh "ARTM" in
  assert (ARTM : forall m', munch (gstr_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> ART RT Σ m') by (intros m' MU WM; exact (lvl_art_munch RT AF E Σ _ m m' ARTg AL (FPW Σ) MU WM));
  let SZN := fresh "SZN" in
  assert (SZN : forall m', munch (gstr_W sp' (sp' + 128)) m m' -> wmono bsegs m m' -> shz m' (f + 208) 16)
    by (intros m' MU WM; apply (fobj_shz RT AF Σ m' (f + 208) 16 (ARTM m' MU WM)); apply (el_elem_fobj RT Σ m' f 0 0 (-8) t); [| exact FRS| exact FPOS| exact F64];
        eapply rw_cells_agree_nw; [exact CS|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; unfold el_shadow_armA in Hx; rewrite el_shadowA_size in Hx; unfold gstr_W; cbn [outside];
        clear - Hx SLO; repeat split; lia);
  pose proof (ael_root_elem E OKE) as [EL NR];
  apply (aevt_evt RT AF PMc MST);

  astep; step; zstep; apply evt_done;
  eapply (aevt_rt RT PMc Σ K _ _
           (gstr_cps_elB RT AF E OKE RC Σ PMc sp' (sp' + 128) (f + 208) 1 (ae_n E - 1) TAPE_MAX_DEPTH _ gp t0 t1 t2 (wz usp) (wz sp') a2 a3 a4 a5 a6 a7
              (wz f) (wz (shad f)) (wz (f + 32)) (wz (f + 96)) s6 s7 (wz (ae_PTR E)) (wz 0) (wz (zlength (ae_p1 E))) (wz (f + 120)) t3 t4 t5 t6 F fc m jr
              FDO MST AL AI EL ltac:(clear; lia) CE ltac:(left; clear - FLO LOR SPR; ul) ltac:(clear - FPOS FLO LLO LOR SPR SPT; ul) ltac:(clear - F64; Z.div_mod_to_equations; lia)
              C128 ltac:(clear; lia) ltac:(rewrite EHI; clear - SPR; lia) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) ltac:(left; clear - FLO LOR SPR; ul)
              ARTg MIg ltac:(rewrite ELO; exact STg) ltac:(rewrite ELO; clear - NEED'; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) FRM SZN));
    [exact FRM|];
  intros c Hc; eexists Σ, _; split; [exact Hc|];
  intros ms' (v & m1 & b16 & g20 & code & RS & (ART1 & MI1 & ST1) & PRES1 & RC1 & CODE) FRM1;
  destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->); cbn [ms_fcsr MS] in FRM1;
  rewrite ret_pc_even by (clear; lia); rewrite ELO in ST1.

Theorem arm5_okA : forall W, arm_cpsA RT PMc W 5.
Proof using AF RC.
  arm_gstr 5.
  apply (aevt_evt RT AF PMc MST).
  assert (OUTm : rw_cells bsegs m1 (sp' + 128) ([] ++ [CB 16 b16; C4 (wz code); CB 4 g20] ++ [])) by (cbn [app]; exact RC1).
  pose proof (rw_cells_merge bsegs m1 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
  zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m1 fc1 F1).
  eapply (arm_post_out RT AF W 5 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m1 fc1 _ LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ART1 MI1 ST1 FRM1);
    [intros ad Ha Hn; cbn [lf_S1] in Ha, Hn; apply (PRES1 ad Ha); cbn [outside]; split; [clear - Hn; lia| exact I]| exact OUTj| reflexivity].
Qed.

Theorem arm12_okA : forall W, arm_cpsA RT PMc W 12.
Proof using AF RC.
  arm_gstr 12.
  apply (aevt_evt RT AF PMc MST).

  step. zstep. astep. step. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in Kc by lia; clear - Kc CODE; lia| clear Kc].
  assert (OUTm : rw_cells bsegs m1 (sp' + 128) ([] ++ [CB 16 b16; C4 (wz code); CB 4 g20] ++ [])) by (cbn [app]; exact RC1).
  pose proof (rw_cells_merge bsegs m1 (sp' + 128) [] _ [] OUTm) as OUTj. cbn [app cells_size csize Nat.add cells_bytes] in OUTj.
  zstep. apply evt_done. apply (POST false (rt_credit RT Σ) Σ m1 fc1 F1).
  eapply (arm_post_out RT AF W 12 (mkLF usp sp' f lo) E Σ sel idx jr jos t m m1 fc1 _ LK OKE (conj EDOC (conj EFD (conj EKD (conj ELO EHI)))) AL FRS ARTg AM ART1 MI1 ST1 FRM1);
    [intros ad Ha Hn; cbn [lf_S1] in Ha, Hn; apply (PRES1 ad Ha); cbn [outside]; split; [clear - Hn; lia| exact I]| exact OUTj| reflexivity].
Qed.
End Arm5.
