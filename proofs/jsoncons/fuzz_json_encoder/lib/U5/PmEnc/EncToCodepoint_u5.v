(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_to_codepoint_xsrc_T_u5 Cut_to_codepoint_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ETC.
Import PMES.
Module G := Cut_to_codepoint_xsrc_u5.
Module GT := Cut_to_codepoint_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition F0 : list SGP.region := CC.cp_F G.cp0.

Lemma cut_facts : CC.cps_all G.CPS (fun _ c => SP.cut_chk GT.NF F0 c) = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma exit_facts : CC.others_all G.CPS G.TAGS (fun _ ps _ =>
  SP.exit_chk GT.ENDS ps && CL.ps_reg_is ps 10 (APC.eaddz (EVar 10) 1) && CL.ps_reg_is ps 11 (ELit 0) &&
  PB.has (SR.ps_cells ps) (KWord (SA (EVar 12) 0) 4 (EVar 32)))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts0 : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.exit_chk GT.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. repeat (destruct H as [<-|H]; [CL.solve_is_ret|]). destruct H. Qed.   (* [comment removed for export] *)

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem to_codepoint_ok : to_codepoint_spec L.
Proof.
  intros it e cpc c sp r fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Ha2 & Ha3 & Hlt & Hu8 & Hc & Himg & Hdef & Hc1 & Hc2 & Hit & He & Hits) Hcont.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by (unfold hl_ceil; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [c] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = it) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = e) by (rewrite (EV 11%bv), Ha1; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = cpc) by (rewrite (EV 12%bv), Ha2; apply u64_of_Z; lia).
  assert (U13 : bv_unsigned (ev E0 13) = 0) by (rewrite (EV 13%bv), Ha3; apply u64_of_Z; lia).
  assert (V32 : ev E0 32 = Z_to_bv 64 c) by reflexivity.
  assert (U32 : bv_unsigned (ev E0 32) = c) by (rewrite V32; apply u64_of_Z; lia).
  unfold PML.cfg. change PC_TO_CODEPOINT with (CC.cp_pc G.cp0).
  eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G.CPS G.TAGS GT.NF F0 GT.ENDS eq_refl ltac:(unfold GT.NF; lia) G.plans G.tags_ok cut_facts exit_facts0 rets
            fx R M model K E0 G.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
  - (* [comment removed for export] *)
    pose proof (PmLayout.ly_segs L LAY) as LS.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply PB2.kword8_intro with (A := it) (z := c); [ev_start | lia | lia | exact V32 | lia | exact Hu8].
    + e_range. + e_range. + e_range.
    + eapply CL5.krange_intro; [lin_eval; rw_atoms; reflexivity | lia | lia].
    + e_range.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros a Ha. apply Himg. unfold PML.IMG_RO_HI. lia.
    + e_unk. + e_wr. + e_range. + e_range. + e_align S1.
    + e_disj.
  - (* [comment removed for export] *)
    intros fx' i c0 tags k ps0 id E' R' M1 M' Hc0 Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
    pose proof (CC.others_all_sound _ _ _ exit_facts i c0 tags k ps0 id Hc0 Htags Hps Htag) as X.
    apply andb_prop in X as [X Xc]. apply andb_prop in X as [X X11]. apply andb_prop in X as [_ X10].
    assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
    apply (Hcont fx' R' M' HFP); [| exact Hrp | | exact Hgr].
    + split; [|split].
      * unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms|lia].
        rewrite <- (proj1 HagE 10%nat ltac:(unfold GT.NF; lia)), U10. lia.
      * rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF X11 eq_refl). reflexivity.
      * pose proof (PB.has_ok E' M' _ _ HK Xc) as HC. apply (PB2.kword32_elim E' M' _ _ cpc) in HC.
        -- unfold PB.uv in HC. cbn [edenot] in HC. rewrite <- (proj1 HagE 32%nat ltac:(unfold GT.NF; lia)), U32 in HC. exact HC.
        -- rewrite (PB.estart_agree GT.NF E0 E' (EVar 12) 0 HagE eq_refl). ev_start.
    + apply (SP.frame_but_of_outside E0 F0 [(sp - 0, 0); (cpc, 4)] M M'); [|exact Hfr].
      intros rb rlo rlen [Hin|[]]. injection Hin as <- <- <-. right. exists (cpc, 4). split; [right; left; reflexivity|]. cbn [fst snd].
      assert (Es : estart E0 (SA (EVar 12) 0) = cpc) by ev_start. assert (El : elenZ E0 (ELit 4) = 4) by ev_len. rewrite Es, El. lia.
Qed.
End S.
End ETC.
