(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_parent_xsrc_T_u5 Cut_parent_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ParentProof.
Module G := Cut_parent_xsrc_u5.
Module GT := Cut_parent_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Definition F0 : list SGP.region := CC.cp_F G.cp0.

Lemma cut_facts : CC.cps_all G.CPS (fun _ c => SP.cut_chk GT.NF F0 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.exit_chk GT.ENDS ps && CL.ps_reg_is ps 10 (EVar 34))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts0 : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.exit_chk GT.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem parent_ok : PMS.parent_spec L.
Proof.
  intros P x sp r ps rest fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & HPA & Hstack & (OP1 & OP2 & OP3) & Hx & Hsb & Hsbs) Hcont.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PML.parser_at in HPA.
  destruct HPA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C248 & C256 & _ & Hbytes & Hlen & _).
  set (sb := PML.ps_sb ps) in *. set (n := Z.of_nat (length (PML.ps_stack ps))) in *.
  assert (Hn : n = Z.of_nat (length rest) + 1) by (unfold n; rewrite Hstack, length_app; cbn [length]; lia).
  assert (Hxb : PML.u8 M (sb + n - 1) x).
  { specialize (Hbytes (length rest) ltac:(rewrite Hstack, length_app; cbn [length]; lia)). rewrite Hstack, app_nth2, Nat.sub_diag in Hbytes by lia. cbn [nth] in Hbytes.
    replace (sb + n - 1) with (sb + Z.of_nat (length rest)) by lia. exact Hbytes. }
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [sb; n; x] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (V32 : ev E0 32 = Z_to_bv 64 sb) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 n) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 x) by reflexivity.
  assert (U32 : bv_unsigned (ev E0 32) = sb) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = n) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = x) by (rewrite V34; apply u64_of_Z; lia).
  unfold PML.cfg. change PML.PC_PARENT with (CC.cp_pc G.cp0).
  eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G.CPS G.TAGS GT.NF F0 GT.ENDS eq_refl ltac:(unfold GT.NF; lia) G.plans G.tags_ok cut_facts exit_facts0 rets
            fx R M model K E0 G.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
  - (* [comment removed for export] *)
    assert (Hds : L5.defined M (sp - 48) 48) by exact S5.
    assert (W256 : edenot E0 (APC.eadd (EVar 32) (EVar 33)) = Z_to_bv 64 (sb + n)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := P + 248) (z := sb); [ev_start | lia | lia | exact V32 | exact C248].
    + eapply CL5.kword64_intro with (A := P + 256) (z := sb + n); [ev_start | lia | lia | exact W256 | exact C256].
    + eapply PB2.kword8_intro with (A := sb + n - 1) (z := x); [rewrite (CL5.estart_lin E0 _ (-1) (sb + n)); [lia | lin_eval; rw_atoms; lia | lia] | lia | lia | exact V34 | lia | exact Hxb].
    + e_range. + e_range. + e_range. + e_range.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj.
    + eapply CL5.kdisj_intro; [ev_start | ev_len | rewrite (CL5.estart_lin E0 _ (-1) (sb + n)); [reflexivity | lin_eval; rw_atoms; lia | lia] | ev_len | lia].
  - (* [comment removed for export] *)
    intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
    pose proof (CC.others_all_sound _ _ _ exit_facts i c tags k ps0 id Hc Htags Hps Htag) as X. apply andb_prop in X as [_ X10].
    apply (Hcont fx' R' M' HFP); [| exact Hrp | | exact Hgr].
    + unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl). cbn [edenot].
      rewrite <- (proj1 HagE 34%nat ltac:(unfold GT.NF; lia)). exact V34.
    + apply (SP.frame_but_of_outside E0 F0 [(sp - 48, 48)] M M'); [|exact Hfr].
      intros rb rlo rlen [Hin|[]]. injection Hin as <- <- <-. right. exists (sp - 48, 48). split; [left; reflexivity|]. cbn [fst snd].
      assert (Es : estart E0 (SA (EVar 2) (-48)) = sp - 48) by ev_start. assert (El : elenZ E0 (ELit 48) = 48) by ev_len. rewrite Es, El. lia.
Qed.
End S.
End ParentProof.
Print Assumptions ParentProof.parent_ok.
