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
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure SmallCall SmallSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_lit_null_first_xsrc_T_u5 Cut_lit_null_first_xsrc_u5 Cut_lit_null_done_xsrc_T_u5 Cut_lit_null_done_xsrc_u5
                    Cut_lit_true_first_xsrc_T_u5 Cut_lit_true_first_xsrc_u5 Cut_lit_true_done_xsrc_T_u5 Cut_lit_true_done_xsrc_u5
                    Cut_lit_false_first_xsrc_T_u5 Cut_lit_false_first_xsrc_u5 Cut_lit_false_done_xsrc_T_u5 Cut_lit_false_done_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ELTN.
Import PMES.
Module G1 := Cut_lit_null_first_xsrc_u5.  Module GT1 := Cut_lit_null_first_xsrc_T_u5.
Module G2 := Cut_lit_null_done_xsrc_u5.   Module GT2 := Cut_lit_null_done_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition S : Z := 0xdb5c8.
Definition GU : Z := 0xdb5c8 + 16.
Definition TXT : Z := 0x10fea.
Definition LEN : Z := 4.
Definition SCR : Z := CH.hd_scr G1.HDECL.
Definition F1 : list SGP.region := CC.cp_F G1.cp0.
Definition F2 : list SGP.region := CC.cp_F G2.cp0.
Definition CALLS1 : list Z := [PML.PC_GUARD_ACQ; PML.PC_GUARD_REL].
(* [comment removed for export] *)
Definition CRS : list SGP.region := [(ELit 0, S, ELit 18)].

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition a0_is (ps : SR.post_spec) (e : expr) : bool := expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) e.
(* [comment removed for export] *)
Definition exit_chk (ps : SR.post_spec) : bool :=
  (CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN) &&
   forallb (PB.has (SR.ps_cells ps)) (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]))%bool.

(* [comment removed for export] *)
Lemma cut_facts2 : CC.cps_all G2.CPS (fun _ c => SP.cut_chk GT2.NF F2 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => SP.exit_chk GT2.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets2 : forall pc, In pc GT2.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Lemma cut_facts1 : CC.cps_all G1.CPS (fun _ c => SP.cut_chk GT1.NF F1 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else SP.exit_chk GT1.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else exit_chk ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets1 : forall pc, In pc GT1.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Definition call_leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if SP.is_call CALLS1 pc then
        if negb (Z.eqb (SR.ps_pc ps) pc) then false else
        match CH2.ret_of G1.RETS i k with
        | Some j => match nth_error G1.CPS j with
                    | Some cj =>
                        let cells := SR.ps_cells ps in
                        if Z.eqb pc PML.PC_GUARD_ACQ then
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps cj)
                           && a0_is ps (ELit GU) && forallb (PB.has cells) (SSU.guard_news (ELit 0) GU 0 0))%bool
                        else
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps cj) && a0_is ps (ELit GU))%bool
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts : CH2.leaves_all G1.CPS G1.TAGS call_leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma gu_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GU) 2 = true.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis ACQ_OK : PMS.guard_acquire_spec L.
Hypothesis REL_OK : PMS.guard_release_spec L.

Theorem null_literal_ok : null_literal_spec L.
Proof.
  intros sp r fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & HLIT & HWR & IMGRO) Hcont.
  pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5). unfold LIT_SCR in *.
  change PML.LIT_NULL_S with S in *. change PML.LIT_NULL_G with GU in *. change PML.LIT_NULL_TXT with TXT in *.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (ESL0 : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (LIT : forall Ex z, 0 <= z < 2 ^ 64 -> PB.uv Ex (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
  assert (FRAME : forall F0 (M' : mem), (forall rb rlo rlen, In (rb, rlo, rlen) F0 -> In (rb, rlo, rlen) F1) ->
            (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> L5.frame_but [(sp - 64, 64); (S, 18)] M M').
  { intros F0 M' Hsub Hfr. apply (SP.frame_but_of_outside E0 F0 _ M M'); [|exact Hfr].
    intros rb rlo rlen Hin. right. specialize (Hsub _ _ _ Hin). unfold F1 in Hsub. cbn [G1.cp0 CC.cp_F In] in Hsub.
    destruct Hsub as [X|[X|[]]]; injection X as <- <- <-.
    - exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia.
    - exists (S, 18). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (ELit 0) 0xdb5c8) = 0xdb5c8) by sp_start. rewrite Es, (ELN E0 18 ltac:(lia)). unfold S. lia. }
  assert (RES : forall E' (M1 M' : mem) c ps0 (R' : bvmap 5 word), CC.leaf_facts RSEGS c ps0 E' R' M1 M' ->
            (CL.ps_reg_is ps0 10 (ELit TXT) && CL.ps_reg_is ps0 11 (ELit LEN))%bool = true -> PML.a0 R' TXT /\ PML.a1 R' LEN).
  { intros E' M1 M' c ps0 R' HLF X. apply andb_prop in X as [X10 X11].
    split; [unfold PML.a0; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl); reflexivity
          |unfold PML.a1; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF X11 eq_refl); reflexivity]. }
  destruct HLIT as [(HG0 & HG1 & HS0 & HS8)|(HG0 & HG1 & HS0 & HS8)].
  - (* [comment removed for export] *)
    assert (NF32' : (32 <= GT1.NF)%nat) by (unfold GT1.NF; lia).
    assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
    assert (SCRV : SCR = 64) by reflexivity.
    assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
    assert (CRS_OK : forall rg, In rg CRS -> SGP.region_vars_lt GT1.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a).
    { intros rg [<-|[]]; (split; [reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
        rewrite ?(u64_of_Z 0) in Ha by lia; rewrite ?(u64_of_Z 18) in Ha by lia; unfold S in Ha; rewrite SCRV.
      lia. }
    assert (WG : forall Mx : mem, L5.writable RSEGS Mx GU 2) by (intros Mx; apply (SP.writable_static RSEGS Mx GU 2 gu_wr); unfold GU, S; lia).
    unfold PML.cfg. change PC_NULL_LIT with (CC.cp_pc G1.cp0).
    eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G1.CPS G1.TAGS GT1.NF F1 GT1.ENDS eq_refl NF32' G1.plans G1.tags_ok cut_facts1 rets1 CALLS1 exit_facts1
              fx R M model K E0 G1.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + (* [comment removed for export] *)
      split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G1.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply PB2.kword8_intro with (A := GU + 1) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG1].
      * eapply CL5.kword64_intro with (A := S) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ S 18); [sp_start | ev_len | unfold S; lia | unfold S; lia | exact HWR].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + (* [comment removed for export] *)
      intros i c tags k ps0 id Hc Htags Hps Htag Hic.
      assert (IL : CH2.is_leaf G1.CPS G1.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
      pose proof (CH2.leaves_all_sound _ _ _ call_facts _ _ _ _ _ IL) as X. unfold call_leaf_chk in X. rewrite Hic in X.
      destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
      destruct (CH2.ret_of G1.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G1.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F1) by (left; reflexivity).
      assert (A0R : forall e z, a0_is ps0 e = true -> regs_ok E' (CA.ps_reglist ps0) R' -> PB.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Ha HR Hz. unfold a0_is in Ha. apply expr_eqb_eq in Ha. rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota.
        change (ridx 10%bv) with 10%nat. rewrite Ha. apply PB.edenot_of_uv. exact Hz. }
      destruct (Z.eqb_spec id PML.PC_GUARD_ACQ) as [->|N1].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ GU (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C1. rewrite LIT in C1 by lia.
        apply (ACQ_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia|]. split; [exact C0|]. split; [exact C1 | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P1 & P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 0); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 2); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
      * (* [comment removed for export] *)
        assert (Hid : id = PML.PC_GUARD_REL).
        { unfold SP.is_call, CALLS1 in Hic. cbn [existsb] in Hic. rewrite (proj2 (Z.eqb_neq _ _) N1) in Hic. cbn [orb] in Hic.
          destruct (Z.eqb_spec id PML.PC_GUARD_REL); [assumption | discriminate]. }
        rewrite Hid. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        apply (REL_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 1); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 1); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
    + (* [comment removed for export] *)
      intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts1 i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X.
      unfold exit_chk in X. apply andb_prop in X as [Xr Xst].
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M') by (apply (FRAME F1 M'); [intros rb rlo rlen Hin; exact Hin | exact Hfr]).
      assert (CELL : forall X, In X (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]) -> kentry_ok RSEGS E' M' X).
      { intros X0 HX. rewrite forallb_forall in Xst. exact (PB.has_ok E' M' _ _ HK (Xst X0 HX)). }
      destruct (RES E' M1 M' c ps0 R' HLF Xr) as [A0 A1].
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|]. split; [|split; [|split]].
      * pose proof (PB2.kword8_elim E' M' _ _ GU (CELL _ ltac:(left; reflexivity)) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (CELL _ ltac:(right; left; reflexivity)) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ S (CELL _ ltac:(right; right; left; reflexivity)) (ESL0 E' S ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold TXT; lia). exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ (S + 8) (CELL _ ltac:(right; right; right; left; reflexivity)) (ESL0 E' (S + 8) ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold LEN; lia). exact C.
  - (* [comment removed for export] *)
    unfold PML.cfg. change PC_NULL_LIT with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 1); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply CL5.kword64_intro with (A := S) (z := TXT); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := LEN); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 64, 64)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[]]; injection X0 as <- <- <-.
        exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia. }
      destruct (RES E' M1 M' c ps0 R' HLF X) as [A0 A1].
      assert (OUT : forall a n, S <= a -> a + n <= S + 18 -> PB2.out [(sp - 64, 64)] a n).
      { intros a n Ha Hn. unfold S in *. split; [lia|]. split; [lia|]. intros j Hj w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG0]|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG1]|].
      split; [apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS0] | apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS8]].
Qed.
End S.
End ELTN.

Module ELTT.
Import PMES.
Module G1 := Cut_lit_true_first_xsrc_u5.  Module GT1 := Cut_lit_true_first_xsrc_T_u5.
Module G2 := Cut_lit_true_done_xsrc_u5.   Module GT2 := Cut_lit_true_done_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition S : Z := 0xdb5e0.
Definition GU : Z := 0xdb5e0 + 16.
Definition TXT : Z := 0x11a2d.
Definition LEN : Z := 4.
Definition SCR : Z := CH.hd_scr G1.HDECL.
Definition F1 : list SGP.region := CC.cp_F G1.cp0.
Definition F2 : list SGP.region := CC.cp_F G2.cp0.
Definition CALLS1 : list Z := [PML.PC_GUARD_ACQ; PML.PC_GUARD_REL].
(* [comment removed for export] *)
Definition CRS : list SGP.region := [(ELit 0, S, ELit 18)].

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition a0_is (ps : SR.post_spec) (e : expr) : bool := expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) e.
(* [comment removed for export] *)
Definition exit_chk (ps : SR.post_spec) : bool :=
  (CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN) &&
   forallb (PB.has (SR.ps_cells ps)) (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]))%bool.

(* [comment removed for export] *)
Lemma cut_facts2 : CC.cps_all G2.CPS (fun _ c => SP.cut_chk GT2.NF F2 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => SP.exit_chk GT2.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets2 : forall pc, In pc GT2.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Lemma cut_facts1 : CC.cps_all G1.CPS (fun _ c => SP.cut_chk GT1.NF F1 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else SP.exit_chk GT1.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else exit_chk ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets1 : forall pc, In pc GT1.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Definition call_leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if SP.is_call CALLS1 pc then
        if negb (Z.eqb (SR.ps_pc ps) pc) then false else
        match CH2.ret_of G1.RETS i k with
        | Some j => match nth_error G1.CPS j with
                    | Some cj =>
                        let cells := SR.ps_cells ps in
                        if Z.eqb pc PML.PC_GUARD_ACQ then
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps cj)
                           && a0_is ps (ELit GU) && forallb (PB.has cells) (SSU.guard_news (ELit 0) GU 0 0))%bool
                        else
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps cj) && a0_is ps (ELit GU))%bool
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts : CH2.leaves_all G1.CPS G1.TAGS call_leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma gu_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GU) 2 = true.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis ACQ_OK : PMS.guard_acquire_spec L.
Hypothesis REL_OK : PMS.guard_release_spec L.

Theorem true_literal_ok : true_literal_spec L.
Proof.
  intros sp r fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & HLIT & HWR & IMGRO) Hcont.
  pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5). unfold LIT_SCR in *.
  change PML.LIT_TRUE_S with S in *. change PML.LIT_TRUE_G with GU in *. change PML.LIT_TRUE_TXT with TXT in *.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (ESL0 : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (LIT : forall Ex z, 0 <= z < 2 ^ 64 -> PB.uv Ex (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
  assert (FRAME : forall F0 (M' : mem), (forall rb rlo rlen, In (rb, rlo, rlen) F0 -> In (rb, rlo, rlen) F1) ->
            (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> L5.frame_but [(sp - 64, 64); (S, 18)] M M').
  { intros F0 M' Hsub Hfr. apply (SP.frame_but_of_outside E0 F0 _ M M'); [|exact Hfr].
    intros rb rlo rlen Hin. right. specialize (Hsub _ _ _ Hin). unfold F1 in Hsub. cbn [G1.cp0 CC.cp_F In] in Hsub.
    destruct Hsub as [X|[X|[]]]; injection X as <- <- <-.
    - exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia.
    - exists (S, 18). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (ELit 0) 0xdb5e0) = 0xdb5e0) by sp_start. rewrite Es, (ELN E0 18 ltac:(lia)). unfold S. lia. }
  assert (RES : forall E' (M1 M' : mem) c ps0 (R' : bvmap 5 word), CC.leaf_facts RSEGS c ps0 E' R' M1 M' ->
            (CL.ps_reg_is ps0 10 (ELit TXT) && CL.ps_reg_is ps0 11 (ELit LEN))%bool = true -> PML.a0 R' TXT /\ PML.a1 R' LEN).
  { intros E' M1 M' c ps0 R' HLF X. apply andb_prop in X as [X10 X11].
    split; [unfold PML.a0; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl); reflexivity
          |unfold PML.a1; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF X11 eq_refl); reflexivity]. }
  destruct HLIT as [(HG0 & HG1 & HS0 & HS8)|(HG0 & HG1 & HS0 & HS8)].
  - (* [comment removed for export] *)
    assert (NF32' : (32 <= GT1.NF)%nat) by (unfold GT1.NF; lia).
    assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
    assert (SCRV : SCR = 64) by reflexivity.
    assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
    assert (CRS_OK : forall rg, In rg CRS -> SGP.region_vars_lt GT1.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a).
    { intros rg [<-|[]]; (split; [reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
        rewrite ?(u64_of_Z 0) in Ha by lia; rewrite ?(u64_of_Z 18) in Ha by lia; unfold S in Ha; rewrite SCRV.
      lia. }
    assert (WG : forall Mx : mem, L5.writable RSEGS Mx GU 2) by (intros Mx; apply (SP.writable_static RSEGS Mx GU 2 gu_wr); unfold GU, S; lia).
    unfold PML.cfg. change PC_TRUE_LIT with (CC.cp_pc G1.cp0).
    eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G1.CPS G1.TAGS GT1.NF F1 GT1.ENDS eq_refl NF32' G1.plans G1.tags_ok cut_facts1 rets1 CALLS1 exit_facts1
              fx R M model K E0 G1.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + (* [comment removed for export] *)
      split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G1.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply PB2.kword8_intro with (A := GU + 1) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG1].
      * eapply CL5.kword64_intro with (A := S) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ S 18); [sp_start | ev_len | unfold S; lia | unfold S; lia | exact HWR].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + (* [comment removed for export] *)
      intros i c tags k ps0 id Hc Htags Hps Htag Hic.
      assert (IL : CH2.is_leaf G1.CPS G1.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
      pose proof (CH2.leaves_all_sound _ _ _ call_facts _ _ _ _ _ IL) as X. unfold call_leaf_chk in X. rewrite Hic in X.
      destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
      destruct (CH2.ret_of G1.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G1.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F1) by (left; reflexivity).
      assert (A0R : forall e z, a0_is ps0 e = true -> regs_ok E' (CA.ps_reglist ps0) R' -> PB.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Ha HR Hz. unfold a0_is in Ha. apply expr_eqb_eq in Ha. rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota.
        change (ridx 10%bv) with 10%nat. rewrite Ha. apply PB.edenot_of_uv. exact Hz. }
      destruct (Z.eqb_spec id PML.PC_GUARD_ACQ) as [->|N1].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ GU (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C1. rewrite LIT in C1 by lia.
        apply (ACQ_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia|]. split; [exact C0|]. split; [exact C1 | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P1 & P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 0); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 2); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
      * (* [comment removed for export] *)
        assert (Hid : id = PML.PC_GUARD_REL).
        { unfold SP.is_call, CALLS1 in Hic. cbn [existsb] in Hic. rewrite (proj2 (Z.eqb_neq _ _) N1) in Hic. cbn [orb] in Hic.
          destruct (Z.eqb_spec id PML.PC_GUARD_REL); [assumption | discriminate]. }
        rewrite Hid. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        apply (REL_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 1); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 1); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
    + (* [comment removed for export] *)
      intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts1 i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X.
      unfold exit_chk in X. apply andb_prop in X as [Xr Xst].
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M') by (apply (FRAME F1 M'); [intros rb rlo rlen Hin; exact Hin | exact Hfr]).
      assert (CELL : forall X, In X (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]) -> kentry_ok RSEGS E' M' X).
      { intros X0 HX. rewrite forallb_forall in Xst. exact (PB.has_ok E' M' _ _ HK (Xst X0 HX)). }
      destruct (RES E' M1 M' c ps0 R' HLF Xr) as [A0 A1].
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|]. split; [|split; [|split]].
      * pose proof (PB2.kword8_elim E' M' _ _ GU (CELL _ ltac:(left; reflexivity)) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (CELL _ ltac:(right; left; reflexivity)) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ S (CELL _ ltac:(right; right; left; reflexivity)) (ESL0 E' S ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold TXT; lia). exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ (S + 8) (CELL _ ltac:(right; right; right; left; reflexivity)) (ESL0 E' (S + 8) ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold LEN; lia). exact C.
  - (* [comment removed for export] *)
    unfold PML.cfg. change PC_TRUE_LIT with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 1); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply CL5.kword64_intro with (A := S) (z := TXT); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := LEN); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 64, 64)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[]]; injection X0 as <- <- <-.
        exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia. }
      destruct (RES E' M1 M' c ps0 R' HLF X) as [A0 A1].
      assert (OUT : forall a n, S <= a -> a + n <= S + 18 -> PB2.out [(sp - 64, 64)] a n).
      { intros a n Ha Hn. unfold S in *. split; [lia|]. split; [lia|]. intros j Hj w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG0]|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG1]|].
      split; [apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS0] | apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS8]].
Qed.
End S.
End ELTT.

Module ELTF.
Import PMES.
Module G1 := Cut_lit_false_first_xsrc_u5.  Module GT1 := Cut_lit_false_first_xsrc_T_u5.
Module G2 := Cut_lit_false_done_xsrc_u5.   Module GT2 := Cut_lit_false_done_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition S : Z := 0xdb5f8.
Definition GU : Z := 0xdb5f8 + 16.
Definition TXT : Z := 0x1030d.
Definition LEN : Z := 5.
Definition SCR : Z := CH.hd_scr G1.HDECL.
Definition F1 : list SGP.region := CC.cp_F G1.cp0.
Definition F2 : list SGP.region := CC.cp_F G2.cp0.
Definition CALLS1 : list Z := [PML.PC_GUARD_ACQ; PML.PC_GUARD_REL].
(* [comment removed for export] *)
Definition CRS : list SGP.region := [(ELit 0, S, ELit 18)].

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition a0_is (ps : SR.post_spec) (e : expr) : bool := expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) e.
(* [comment removed for export] *)
Definition exit_chk (ps : SR.post_spec) : bool :=
  (CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN) &&
   forallb (PB.has (SR.ps_cells ps)) (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]))%bool.

(* [comment removed for export] *)
Lemma cut_facts2 : CC.cps_all G2.CPS (fun _ c => SP.cut_chk GT2.NF F2 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => SP.exit_chk GT2.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => CL.ps_reg_is ps 10 (ELit TXT) && CL.ps_reg_is ps 11 (ELit LEN))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets2 : forall pc, In pc GT2.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

(* [comment removed for export] *)
Lemma cut_facts1 : CC.cps_all G1.CPS (fun _ c => SP.cut_chk GT1.NF F1 c) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exit_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else SP.exit_chk GT1.ENDS ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma res_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else exit_chk ps) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets1 : forall pc, In pc GT1.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Definition call_leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if SP.is_call CALLS1 pc then
        if negb (Z.eqb (SR.ps_pc ps) pc) then false else
        match CH2.ret_of G1.RETS i k with
        | Some j => match nth_error G1.CPS j with
                    | Some cj =>
                        let cells := SR.ps_cells ps in
                        if Z.eqb pc PML.PC_GUARD_ACQ then
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps cj)
                           && a0_is ps (ELit GU) && forallb (PB.has cells) (SSU.guard_news (ELit 0) GU 0 0))%bool
                        else
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps cj) && a0_is ps (ELit GU))%bool
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts : CH2.leaves_all G1.CPS G1.TAGS call_leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma gu_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GU) 2 = true.
Proof. vm_compute. reflexivity. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis ACQ_OK : PMS.guard_acquire_spec L.
Hypothesis REL_OK : PMS.guard_release_spec L.

Theorem false_literal_ok : false_literal_spec L.
Proof.
  intros sp r fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & HLIT & HWR & IMGRO) Hcont.
  pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5). unfold LIT_SCR in *.
  change PML.LIT_FALSE_S with S in *. change PML.LIT_FALSE_G with GU in *. change PML.LIT_FALSE_TXT with TXT in *.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (ESL0 : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
  assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
  assert (LIT : forall Ex z, 0 <= z < 2 ^ 64 -> PB.uv Ex (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
  assert (FRAME : forall F0 (M' : mem), (forall rb rlo rlen, In (rb, rlo, rlen) F0 -> In (rb, rlo, rlen) F1) ->
            (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> L5.frame_but [(sp - 64, 64); (S, 18)] M M').
  { intros F0 M' Hsub Hfr. apply (SP.frame_but_of_outside E0 F0 _ M M'); [|exact Hfr].
    intros rb rlo rlen Hin. right. specialize (Hsub _ _ _ Hin). unfold F1 in Hsub. cbn [G1.cp0 CC.cp_F In] in Hsub.
    destruct Hsub as [X|[X|[]]]; injection X as <- <- <-.
    - exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia.
    - exists (S, 18). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (ELit 0) 0xdb5f8) = 0xdb5f8) by sp_start. rewrite Es, (ELN E0 18 ltac:(lia)). unfold S. lia. }
  assert (RES : forall E' (M1 M' : mem) c ps0 (R' : bvmap 5 word), CC.leaf_facts RSEGS c ps0 E' R' M1 M' ->
            (CL.ps_reg_is ps0 10 (ELit TXT) && CL.ps_reg_is ps0 11 (ELit LEN))%bool = true -> PML.a0 R' TXT /\ PML.a1 R' LEN).
  { intros E' M1 M' c ps0 R' HLF X. apply andb_prop in X as [X10 X11].
    split; [unfold PML.a0; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl); reflexivity
          |unfold PML.a1; rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF X11 eq_refl); reflexivity]. }
  destruct HLIT as [(HG0 & HG1 & HS0 & HS8)|(HG0 & HG1 & HS0 & HS8)].
  - (* [comment removed for export] *)
    assert (NF32' : (32 <= GT1.NF)%nat) by (unfold GT1.NF; lia).
    assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
    assert (SCRV : SCR = 64) by reflexivity.
    assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
    assert (CRS_OK : forall rg, In rg CRS -> SGP.region_vars_lt GT1.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a).
    { intros rg [<-|[]]; (split; [reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha;
        rewrite ?(u64_of_Z 0) in Ha by lia; rewrite ?(u64_of_Z 18) in Ha by lia; unfold S in Ha; rewrite SCRV.
      lia. }
    assert (WG : forall Mx : mem, L5.writable RSEGS Mx GU 2) by (intros Mx; apply (SP.writable_static RSEGS Mx GU 2 gu_wr); unfold GU, S; lia).
    unfold PML.cfg. change PC_FALSE_LIT with (CC.cp_pc G1.cp0).
    eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G1.CPS G1.TAGS GT1.NF F1 GT1.ENDS eq_refl NF32' G1.plans G1.tags_ok cut_facts1 rets1 CALLS1 exit_facts1
              fx R M model K E0 G1.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + (* [comment removed for export] *)
      split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G1.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply PB2.kword8_intro with (A := GU + 1) (z := 0); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG1].
      * eapply CL5.kword64_intro with (A := S) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := 0); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ S 18); [sp_start | ev_len | unfold S; lia | unfold S; lia | exact HWR].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + (* [comment removed for export] *)
      intros i c tags k ps0 id Hc Htags Hps Htag Hic.
      assert (IL : CH2.is_leaf G1.CPS G1.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
      pose proof (CH2.leaves_all_sound _ _ _ call_facts _ _ _ _ _ IL) as X. unfold call_leaf_chk in X. rewrite Hic in X.
      destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
      destruct (CH2.ret_of G1.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G1.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F1) by (left; reflexivity).
      assert (A0R : forall e z, a0_is ps0 e = true -> regs_ok E' (CA.ps_reglist ps0) R' -> PB.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Ha HR Hz. unfold a0_is in Ha. apply expr_eqb_eq in Ha. rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota.
        change (ridx 10%bv) with 10%nat. rewrite Ha. apply PB.edenot_of_uv. exact Hz. }
      destruct (Z.eqb_spec id PML.PC_GUARD_ACQ) as [->|N1].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 0 2) (Some (ELit 1)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ GU (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C1. rewrite LIT in C1 by lia.
        apply (ACQ_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia|]. split; [exact C0|]. split; [exact C1 | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P1 & P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 0); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 2); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
      * (* [comment removed for export] *)
        assert (Hid : id = PML.PC_GUARD_REL).
        { unfold SP.is_call, CALLS1 in Hic. cbn [existsb] in Hic. rewrite (proj2 (Z.eqb_neq _ _) N1) in Hic. cbn [orb] in Hic.
          destruct (Z.eqb_spec id PML.PC_GUARD_REL); [assumption | discriminate]. }
        rewrite Hid. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GU, ELit 2)] (SSU.guard_news (ELit 0) GU 1 1) None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        apply (REL_OK GU (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GU Xa0 HR (LIT E' GU ltac:(unfold GU, S; lia)))|]. split; [unfold GU, S; lia | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GU, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GU, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL0 E' GU ltac:(unfold GU, S; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), S, (ELit 18). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL0 E0 S ltac:(unfold S; lia)), (ELN E0 18 ltac:(lia)). unfold GU, S. lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := GU) (z := 1); [exact (ESL0 _ GU ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := GU + 1) (z := 1); [exact (ESL0 _ (GU + 1) ltac:(unfold GU, S; lia)) | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact P3].
    + (* [comment removed for export] *)
      intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts1 i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X.
      unfold exit_chk in X. apply andb_prop in X as [Xr Xst].
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M') by (apply (FRAME F1 M'); [intros rb rlo rlen Hin; exact Hin | exact Hfr]).
      assert (CELL : forall X, In X (SSU.guard_news (ELit 0) GU 1 1 ++ [KWord (SA (ELit 0) S) 8 (ELit TXT); KWord (SA (ELit 0) (S + 8)) 8 (ELit LEN)]) -> kentry_ok RSEGS E' M' X).
      { intros X0 HX. rewrite forallb_forall in Xst. exact (PB.has_ok E' M' _ _ HK (Xst X0 HX)). }
      destruct (RES E' M1 M' c ps0 R' HLF Xr) as [A0 A1].
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|]. split; [|split; [|split]].
      * pose proof (PB2.kword8_elim E' M' _ _ GU (CELL _ ltac:(left; reflexivity)) (ESL0 E' GU ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword8_elim E' M' _ _ (GU + 1) (CELL _ ltac:(right; left; reflexivity)) (ESL0 E' (GU + 1) ltac:(unfold GU, S; lia))) as C. rewrite LIT in C by lia. exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ S (CELL _ ltac:(right; right; left; reflexivity)) (ESL0 E' S ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold TXT; lia). exact C.
      * pose proof (PB2.kword64_elim E' M' _ _ (S + 8) (CELL _ ltac:(right; right; right; left; reflexivity)) (ESL0 E' (S + 8) ltac:(unfold S; lia))) as C. rewrite LIT in C by (unfold LEN; lia). exact C.
  - (* [comment removed for export] *)
    unfold PML.cfg. change PC_FALSE_LIT with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := GU) (z := 1); [sp_start | unfold GU, S; lia | unfold GU, S; lia | reflexivity | lia | exact HG0].
      * eapply CL5.kword64_intro with (A := S) (z := TXT); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS0].
      * eapply CL5.kword64_intro with (A := S + 8) (z := LEN); [sp_start | unfold S; lia | unfold S; lia | reflexivity | exact HS8].
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ res_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (FB : L5.frame_but [(sp - 64, 64); (S, 18)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 64, 64)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[]]; injection X0 as <- <- <-.
        exists (sp - 64, 64). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-64)) = sp - 64) by ev_start. rewrite Es, (ELN E0 64 ltac:(lia)). lia. }
      destruct (RES E' M1 M' c ps0 R' HLF X) as [A0 A1].
      assert (OUT : forall a n, S <= a -> a + n <= S + 18 -> PB2.out [(sp - 64, 64)] a n).
      { intros a n Ha Hn. unfold S in *. split; [lia|]. split; [lia|]. intros j Hj w [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact A0|]. split; [exact A1|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG0]|].
      split; [apply (PB2.u8_fr _ M M' FB2); [apply OUT; unfold GU, S; lia | exact HG1]|].
      split; [apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS0] | apply (PB2.u64_fr _ M M' FB2); [apply OUT; lia | exact HS8]].
Qed.
End S.
End ELTF.

