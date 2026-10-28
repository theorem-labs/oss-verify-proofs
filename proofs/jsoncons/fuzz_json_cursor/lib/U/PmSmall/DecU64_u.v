(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_dec_u64_csrc_T_u Cut_dec_u64_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module DecU64Proof.
Module G := Cut_dec_u64_csrc_u.
Module GT := Cut_dec_u64_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Definition F0 : list SGP.region := CC.cp_F G.cp0.

Lemma cut_facts : CC.cps_all G.CPS (fun _ c => SP.cut_chk GT.NF F0 c) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts0 : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.exit_chk GT.ENDS ps) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts : CC.others_all G.CPS G.TAGS (fun _ ps _ => SP.lit_in (SP.reg_of ps 11) [0; 22; 34]) = true.
Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [GT.ENDS In] in H. repeat (destruct H as [<-|H]; [CL.solve_is_ret|]). destruct H. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem dec_u64_ok : PMS.dec_u64_spec L.
Proof.
  intros s len vp sp r fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Ha2 & Hlen & Hdefs & Hdefv & Hvp1 & Hvp2 & IMGRO & Hs1 & Hs2) Hcont.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMS.PF_SCR in *.
  destruct (PB.bytes_of_defined M (Z.to_nat len) s ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; exact Hdefs)) as (bs & Hbl & Hbs).
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun id => match id with 0%nat => map (Z_to_bv 8) bs | _ => [] end)).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite (EV 11%bv), Ha1; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = vp) by (rewrite (EV 12%bv), Ha2; apply u64_of_Z; lia).
  assert (Hbl' : Z.of_nat (length bs) = len) by (rewrite Hbl; lia).
  unfold PML.cfg. change PML.PC_DEC_U64 with (CC.cp_pc G.cp0).
  eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G.CPS G.TAGS GT.NF F0 GT.ENDS eq_refl ltac:(unfold GT.NF; lia) G.plans G.tags_ok cut_facts exit_facts0 rets
            fx R M model K E0 G.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
  -
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kblob_intro with (bs := bs) (A := s); [ev_start | unfold elenZ; cbn [edenot]; rewrite U11; lia | lia | lia | lia | reflexivity | exact Hbs | rewrite Hbl'; exact Hdefs].
    + sp_unk Hdefs.
    + e_range. + e_range.
    + sp_unk Hdefv.
    + sp_wr Hdefv.
    + e_range.
    + cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + sp_disj.
  -
    intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
    pose proof (CC.others_all_sound _ _ _ exit_facts i c tags k ps0 id Hc Htags Hps Htag) as X.
    apply SP.lit_in_sound in X as (z & Hreg & Hz).
    apply (Hcont fx' R' M' HFP); [| exact Hrp | | exact Hgr].
    + exists (bv_unsigned (getr R' 10%bv)), z. split; [unfold PML.a0; symmetry; apply Z_to_bv_bv_unsigned|]. split; [|exact Hz].
      rewrite (SP.reg_of_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF Hreg eq_refl). reflexivity.
    + apply (SP.frame_but_of_outside E0 F0 [(sp - 16, 16); (vp, 8)] M M'); [|exact Hfr].
      intros rb rlo rlen [Hin|[]]; injection Hin as <- <- <-; right.
      exists (vp, 8). split; [right; left; reflexivity|]. cbn [fst snd].
      assert (Es : estart E0 (SA (EVar 12) 0) = vp) by ev_start. assert (El : elenZ E0 (ELit 8) = 8) by ev_len. rewrite Es, El. lia.
Qed.
End S.
End DecU64Proof.

