(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallCall SmallSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_set_ec_ls1_csrc_T_u Cut_set_ec_ls1_csrc_u Cut_set_ec_ls2_csrc_T_u Cut_set_ec_ls2_csrc_u Cut_set_ec_c1_csrc_T_u Cut_set_ec_c1_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SetEcProof.
Module G1 := Cut_set_ec_ls1_csrc_u.  Module GT1 := Cut_set_ec_ls1_csrc_T_u.
Module G2 := Cut_set_ec_ls2_csrc_u.  Module GT2 := Cut_set_ec_ls2_csrc_T_u.
Module G3 := Cut_set_ec_c1_csrc_u.  Module GT3 := Cut_set_ec_c1_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition GUARD : Z := 0xd4df8.
Definition AX : Z := 0xf6848.
Definition SCR : Z := CH.hd_scr G1.HDECL.
Definition F1 : list SGP.region := CC.cp_F G1.cp0.
Definition F2 : list SGP.region := CC.cp_F G2.cp0.
Definition F3 : list SGP.region := CC.cp_F G3.cp0.
Definition CALLS1 : list Z := [PML.PC_GUARD_ACQ; PML.PC_CXA_ATEXIT; PML.PC_GUARD_REL].
Definition Eb : expr := EVar 10.

Definition CRS : list SGP.region := [(ELit 0, GUARD, ELit 2); (ELit 0, AX, ELit 544); (Eb, 0, ELit 16)].

Definition ec_chk (ps : SR.post_spec) : bool :=
  (PB.has (SR.ps_cells ps) (KWord (SA Eb 0) 8 (EVar 11)) && PB.has (SR.ps_cells ps) (KWord (SA Eb 8) 8 (ELit PML.OBJ_JSON_CATEGORY)) && CL.ps_reg_is ps 10 Eb)%bool.
Definition statics_chk (ps : SR.post_spec) : bool :=
  forallb (PB.has (SR.ps_cells ps)) (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)).

Lemma cut_facts2 : CC.cps_all G2.CPS (fun _ c => SP.cut_chk GT2.NF F2 c) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => SP.exit_chk GT2.ENDS ps) = true.
Proof. vmc_refl. Qed.
Lemma ec_facts2 : CC.others_all G2.CPS G2.TAGS (fun _ ps _ => ec_chk ps) = true.
Proof. vmc_refl. Qed.
Lemma rets2 : forall pc, In pc GT2.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Lemma cut_facts1 : CC.cps_all G1.CPS (fun _ c => SP.cut_chk GT1.NF F1 c) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else SP.exit_chk GT1.ENDS ps) = true.
Proof. vmc_refl. Qed.
Lemma ec_facts1 : CC.others_all G1.CPS G1.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else (ec_chk ps && statics_chk ps)%bool) = true.
Proof. vmc_refl. Qed.
Lemma rets1 : forall pc, In pc GT1.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition a0_is (ps : SR.post_spec) (e : expr) : bool := expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) e.

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
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 0 2) (Some (ELit 1)) c ps cj)
                           && a0_is ps (ELit GUARD) && forallb (PB.has cells) (SSU.guard_news (ELit 0) GUARD 0 0))%bool
                        else if Z.eqb pc PML.PC_CXA_ATEXIT then
                          (isSome (SPC.call_chk GT1.NF SCR CRS 128 0 [(ELit 0, AX, ELit 544)] (SSU.atexit_news AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) (Some (ELit 0)) c ps cj)
                           && a0_is ps (ELit PML.ATEXIT_HANDLER) && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) (ELit PML.OBJ_JSON_CATEGORY)
                           && forallb (PB.has cells) [KWord (SA (ELit 0) AX) 1 (ELit 0); KWord (SA (ELit 0) (AX + 4)) 4 (ELit 0); KWord (SA (ELit 0) (AX + 8)) 4 (ELit 1); KWord (SA (ELit 0) (AX + 16)) 8 (ELit (AX + 24)); KWord (SA (ELit 0) (AX + 24)) 8 (ELit 0);
                                                      KWord (SA (ELit 0) (AX + 32)) 8 (ELit PML.ATEXIT_CALL); KWord (SA (ELit 0) (AX + 288)) 8 (ELit PML.AEF_EXIT_GUARD)])%bool
                        else
                          (isSome (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 1 1) None c ps cj) && a0_is ps (ELit GUARD))%bool
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts : CH2.leaves_all G1.CPS G1.TAGS call_leaf_chk = true.
Proof. vmc_refl. Qed.

Definition statics_chk3 (ps : SR.post_spec) : bool :=
  forallb (PB.has (SR.ps_cells ps)) (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news2 AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD PML.ATEXIT_HANDLER PML.OBJ_CONV_CATEGORY (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)).

Lemma cut_facts3 : CC.cps_all G3.CPS (fun _ c => SP.cut_chk GT3.NF F3 c) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts3 : CC.others_all G3.CPS G3.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else SP.exit_chk GT3.ENDS ps) = true.
Proof. vmc_refl. Qed.
Lemma ec_facts3 : CC.others_all G3.CPS G3.TAGS (fun _ ps id => if SP.is_call CALLS1 id then true else (ec_chk ps && statics_chk3 ps)%bool) = true.
Proof. vmc_refl. Qed.
Lemma rets3 : forall pc, In pc GT3.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Definition call_leaf_chk3 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if SP.is_call CALLS1 pc then
        if negb (Z.eqb (SR.ps_pc ps) pc) then false else
        match CH2.ret_of G3.RETS i k with
        | Some j => match nth_error G3.CPS j with
                    | Some cj =>
                        let cells := SR.ps_cells ps in
                        if Z.eqb pc PML.PC_GUARD_ACQ then
                          (isSome (SPC.call_chk GT3.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 0 2) (Some (ELit 1)) c ps cj)
                           && a0_is ps (ELit GUARD) && forallb (PB.has cells) (SSU.guard_news (ELit 0) GUARD 0 0))%bool
                        else if Z.eqb pc PML.PC_CXA_ATEXIT then
                          (isSome (SPC.call_chk GT3.NF SCR CRS 128 0 [(ELit 0, AX, ELit 544)] (SSU.atexit_news2 AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD PML.ATEXIT_HANDLER PML.OBJ_CONV_CATEGORY (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) (Some (ELit 0)) c ps cj)
                           && a0_is ps (ELit PML.ATEXIT_HANDLER) && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) (ELit PML.OBJ_JSON_CATEGORY)
                           && forallb (PB.has cells) [KWord (SA (ELit 0) AX) 1 (ELit 0); KWord (SA (ELit 0) (AX + 4)) 4 (ELit 0); KWord (SA (ELit 0) (AX + 8)) 4 (ELit 2); KWord (SA (ELit 0) (AX + 16)) 8 (ELit (AX + 24)); KWord (SA (ELit 0) (AX + 24)) 8 (ELit 0);
                                                      KWord (SA (ELit 0) (AX + 32)) 8 (ELit PML.ATEXIT_CALL); KWord (SA (ELit 0) (AX + 288)) 8 (ELit PML.AEF_EXIT_GUARD);
                                                      KWord (SA (ELit 0) (AX + 40)) 8 (ELit PML.ATEXIT_HANDLER); KWord (SA (ELit 0) (AX + 296)) 8 (ELit PML.OBJ_CONV_CATEGORY)])%bool
                        else
                          (isSome (SPC.call_chk GT3.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 1 1) None c ps cj) && a0_is ps (ELit GUARD))%bool
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts3 : CH2.leaves_all G3.CPS G3.TAGS call_leaf_chk3 = true.
Proof. vmc_refl. Qed.

Lemma guard_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 GUARD) 2 = true.
Proof. vmc_refl. Qed.
Lemma atexit_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 AX) 544 = true.
Proof. vmc_refl. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis ACQ_OK : PMS.guard_acquire_spec L.
Hypothesis REL_OK : PMS.guard_release_spec L.
Hypothesis ATEXIT_OK : PMS.cxa_atexit_spec L.
Hypothesis ATEXIT2_OK : PMS.cxa_atexit2_spec L.

Lemma ec_exit : forall E' (M M' : mem) ps E code, know_ok RSEGS E' M' (SR.ps_cells ps) -> ec_chk ps = true ->
  PB.uv E' Eb = E -> PB.uv E' (EVar 11) = code -> 1 <= code <= 31 -> 0 <= E -> E + 16 <= 2 ^ 64 -> L5.defined M E 16 -> mem_grows M M' ->
  PML.ec_at M' E code.
Proof.
  intros E' M M' ps E code HK X HE Hcode Hc HE0 HE1 Hdef Hgr. unfold ec_chk in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X0 X8].
  assert (ES : forall k, estart E' (SA Eb k) = E + k) by (intros k; unfold estart; cbn [a_base a_off]; fold (PB.uv E' Eb); rewrite HE; reflexivity).
  pose proof (PB2.kword64_elim E' M' _ _ (E + 0) (PB.has_ok E' M' _ _ HK X0) (ES 0)) as C0. rewrite Hcode, Z.add_0_r in C0.
  pose proof (PB2.kword64_elim E' M' _ _ (E + 8) (PB.has_ok E' M' _ _ HK X8) (ES 8)) as C8. rewrite PB2.uv_lit in C8 by (unfold PML.OBJ_JSON_CATEGORY; lia).
  split; [exact (SP.u64_u32_low RSEGS M' E code C0)|]. split; [intros i Hi; apply Hgr; exact (Hdef i Hi)|]. right. split; [exact Hc | exact C8].
Qed.

Theorem set_ec_ok : PMS.set_ec_spec L.
Proof.
  intros E code sp r g fx R M model K Hh Hl HK0 Hfp ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Hcode & HdefE & (OE1 & OE2 & OE3) & HLS & HG) Hcont.
  pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5). unfold PMS.SETEC_SCR in *.
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = E) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = code) by (rewrite (EV 11%bv), Ha1; apply u64_of_Z; lia).
  assert (FRAME : forall F0 (M' : mem), (forall rb rlo rlen, In (rb, rlo, rlen) F0 -> In (rb, rlo, rlen) F1) ->
            (forall a : word, SGP.outside E0 F0 a -> M' a = M a) -> L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M').
  { intros F0 M' Hsub Hfr. apply (SP.frame_but_of_outside E0 F0 _ M M'); [|exact Hfr].
    intros rb rlo rlen Hin. right. specialize (Hsub _ _ _ Hin). unfold F1 in Hsub. cbn [G1.cp0 CC.cp_F In] in Hsub.
    destruct Hsub as [X|[X|[X|[X|[]]]]]; injection X as <- <- <-.
    - exists (sp - 256, 256). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-256)) = sp - 256) by ev_start. assert (El : elenZ E0 (ELit 256) = 256) by ev_len. rewrite Es, El. lia.
    - exists (E, 16). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 10) 0) = E) by ev_start. assert (El : elenZ E0 (ELit 16) = 16) by ev_len. rewrite Es, El. lia.
    - exists (0xd4df8, 2). split; [right; right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (ELit 0) 0xd4df8) = 0xd4df8) by sp_start. assert (El : elenZ E0 (ELit 2) = 2) by ev_len. rewrite Es, El. lia.
    - exists (0xf6848, 544). split; [right; right; right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (ELit 0) 0xf6848) = 0xf6848) by sp_start. assert (El : elenZ E0 (ELit 544) = 544) by ev_len. rewrite Es, El. lia. }

  assert (LQF : forall M' : mem, L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M' -> PML.libc_quiet M -> PML.libc_quiet M').
  { intros M' FB (Q1 & Q2). unfold PML.libc_quiet in *.
    assert (OUTQ : forall a n, PML.NEED_LOCKS <= a -> a + n <= PML.LOCALE_LOCK + 4 -> PB2.out [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] a n).
    { unfold PML.NEED_LOCKS, PML.LOCALE_LOCK. intros a n Ha Hn. split; [lia|]. split; [lia|]. intros j Hj w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
    split; [apply (PB2.u8_fr _ M M' FB); [apply OUTQ; unfold PML.NEED_LOCKS, PML.LOCALE_LOCK; lia | exact Q1] | apply (PB2.u32_fr _ M M' FB); [apply OUTQ; unfold PML.NEED_LOCKS, PML.LOCALE_LOCK; lia | exact Q2]]. }
  destruct g as [| | | | |]; [exfalso; apply HG; reflexivity | | | | |].
  -
    destruct HLS as (IMGRO & LQ & LD & (HG0 & HG1) & (HC0 & HC1) & (HA0 & HA4 & HA8 & HA16 & HA24 & HA32 & HA288 & _)). cbn [length Z.of_nat Z.add] in HA8. unfold PML.ATEXIT_CALL in HA32. unfold PML.AEF_EXIT_GUARD in HA288.
    assert (WG : forall Mx : mem, L5.writable RSEGS Mx GUARD 2) by (intros Mx; apply (SP.writable_static RSEGS Mx GUARD 2 guard_wr); unfold GUARD; lia).
    assert (WA : forall Mx : mem, L5.writable RSEGS Mx AX 544) by (intros Mx; apply (SP.writable_static RSEGS Mx AX 544 atexit_wr); unfold AX; lia).
    assert (NF32' : (32 <= GT1.NF)%nat) by (unfold GT1.NF; lia).
    assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
    assert (SCRV : SCR = 256) by reflexivity.
    assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
    assert (CRS_OK : forall rg, In rg CRS -> SGP.region_vars_lt GT1.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a).
    { intros rg [<-|[<-|[<-|[]]]]; (split; [reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot Eb] in Ha; rewrite ?U10 in Ha;
        rewrite ?(u64_of_Z 0) in Ha by lia; rewrite ?(u64_of_Z 2), ?(u64_of_Z 544), ?(u64_of_Z 16) in Ha by lia; unfold GUARD, AX in Ha; rewrite SCRV; lia. }
    unfold PML.cfg. change PML.PC_SET_EC with (CC.cp_pc G1.cp0).
    eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G1.CPS G1.TAGS GT1.NF F1 GT1.ENDS eq_refl NF32' G1.plans G1.tags_ok cut_facts1 rets1 CALLS1 exit_facts1
              fx R M model K E0 G1.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    +
      split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G1.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := 0xd4df8) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HG0].
      * eapply PB2.kword8_intro with (A := 0xd4df9) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HG1].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ GUARD 2); [sp_start | ev_len | unfold GUARD; lia | unfold GUARD; lia | exact (WG M)].
      * eapply PB2.kword8_intro with (A := 0xf6848) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HA0].
      * eapply PB.kword32_intro with (A := 0xf684c) (z := 0); [sp_start | lia | lia | reflexivity | exact HA4].
      * eapply PB.kword32_intro with (A := 0xf6850) (z := 1); [sp_start | lia | lia | reflexivity | exact HA8].
      * eapply CL5.kword64_intro with (A := 0xf6858) (z := 0xf6860); [sp_start | lia | lia | reflexivity | exact HA16].
      * eapply CL5.kword64_intro with (A := 0xf6860) (z := 0); [sp_start | lia | lia | reflexivity | exact HA24].
      * eapply CL5.kword64_intro with (A := 0xf6868) (z := 0xa710c); [sp_start | lia | lia | reflexivity | exact HA32].
      * eapply CL5.kword64_intro with (A := 0xf6968) (z := 0x39674); [sp_start | lia | lia | reflexivity | exact HA288].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ AX 544); [sp_start | ev_len | unfold AX; lia | unfold AX; lia | exact (WA M)].
      * sp_unk HdefE. * sp_wr HdefE. * e_range. * e_range.
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
      * sp_disj. * sp_disj.
    +
      intros i c tags k ps0 id Hc Htags Hps Htag Hic.
      assert (IL : CH2.is_leaf G1.CPS G1.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
      pose proof (CH2.leaves_all_sound _ _ _ call_facts _ _ _ _ _ IL) as X. unfold call_leaf_chk in X. rewrite Hic in X.
      destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
      destruct (CH2.ret_of G1.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G1.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F1) by (left; reflexivity).
      assert (ESL : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
      assert (LIT : forall Ex z, 0 <= z < 2 ^ 64 -> PB.uv Ex (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
      assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
      assert (A0R : forall e z, a0_is ps0 e = true -> regs_ok E' (CA.ps_reglist ps0) R' -> PB.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Ha HR Hz. unfold a0_is in Ha. apply expr_eqb_eq in Ha. rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota.
        change (ridx 10%bv) with 10%nat. rewrite Ha. apply PB.edenot_of_uv. exact Hz. }
      destruct (Z.eqb_spec id PML.PC_GUARD_ACQ) as [->|N1]; [|destruct (Z.eqb_spec id PML.PC_CXA_ATEXIT) as [->|N2]].
      *
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 0 2) (Some (ELit 1)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ 0xd4df8 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL E' 0xd4df8 ltac:(lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword8_elim E' M' _ _ 0xd4df9 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL E' 0xd4df9 ltac:(lia))) as C1. rewrite LIT in C1 by lia.
        apply (ACQ_OK GUARD (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GUARD Xa0 HR (LIT E' GUARD ltac:(unfold GUARD; lia)))|]. split; [unfold GUARD; lia|]. split; [exact C0|]. split; [exact C1 | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P1 & P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GUARD, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GUARD, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' GUARD ltac:(unfold GUARD; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), GUARD, (ELit 2). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 GUARD ltac:(unfold GUARD; lia)), (ELN E0 2 ltac:(lia)). lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := 0xd4df8) (z := 0); [exact (ESL _ 0xd4df8 ltac:(lia)) | lia | lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := 0xd4df9) (z := 2); [exact (ESL _ 0xd4df9 ltac:(lia)) | lia | lia | reflexivity | lia | exact P3].
      *
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa1]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 128 0 [(ELit 0, AX, ELit 544)] (SSU.atexit_news AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) (Some (ELit 0)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    128 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ 0xf6848 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL E' 0xf6848 ltac:(lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword32_elim E' M' _ _ 0xf684c (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL E' 0xf684c ltac:(lia))) as C4. rewrite LIT in C4 by lia.
        pose proof (PB2.kword32_elim E' M' _ _ 0xf6850 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; left; reflexivity))) (ESL E' 0xf6850 ltac:(lia))) as C8. rewrite LIT in C8 by lia.
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6858 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; right; left; reflexivity))) (ESL E' 0xf6858 ltac:(lia))) as C16. rewrite LIT in C16 by (unfold AX; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6860 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; right; right; left; reflexivity))) (ESL E' 0xf6860 ltac:(lia))) as C24. rewrite LIT in C24 by lia.
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6868 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 5 right; left; reflexivity))) (ESL E' 0xf6868 ltac:(lia))) as C32. rewrite LIT in C32 by (unfold PML.ATEXIT_CALL; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6968 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 6 right; left; reflexivity))) (ESL E' 0xf6968 ltac:(lia))) as C288. rewrite LIT in C288 by (unfold PML.AEF_EXIT_GUARD; lia).
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 PML.OBJ_JSON_CATEGORY).
        { apply expr_eqb_eq in Xa1. rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Xa1. reflexivity. }
        apply (ATEXIT_OK PML.ATEXIT_HANDLER PML.OBJ_JSON_CATEGORY (bv_unsigned (getr R' 12%bv)) (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ PML.ATEXIT_HANDLER Xa0 HR (LIT E' PML.ATEXIT_HANDLER ltac:(unfold PML.ATEXIT_HANDLER; lia)))|]. split; [exact Ga1|].
          split; [unfold PML.a2; symmetry; apply Z_to_bv_bv_unsigned|]. split; [|split; [exact (WA M') | exact (LQF M' (FRAME F1 M' (fun _ _ _ H => H) Gfr) LQ)]].
          split; [exact C0 | split; [exact C4 | split; [exact C8 | split; [exact C16 | split; [exact C24 | split; [exact C32 | split; [exact C288 | exact I]]]]]]]. }
        intros fx2 R2 M2 HFP2 (P1 & Q0 & Q4 & Q8 & Q16 & Q24 & Q32 & Q288 & Q40 & Q296) Hrp2 Hfb2 Hgr2. unfold PML.cfg. unfold PML.ATEXIT_CALL in Q32. unfold PML.AEF_EXIT_GUARD in Q288.
        apply (CONT fx2 R2 M2 [] [(AX, 544)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, AX, ELit 544). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' AX ltac:(unfold AX; lia)), (ELN E' 544 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 128 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), AX, (ELit 544). split; [right; right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 AX ltac:(unfold AX; lia)), (ELN E0 544 ltac:(lia)). lia.
        -- cbn [length Z.of_nat Z.add] in Q8. intros X0 HX _. unfold SSU.atexit_news, AX in HX. cbn [In] in HX.
           destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
           ++ eapply PB2.kword8_intro with (A := 0xf6848) (z := 0); [exact (ESL _ 0xf6848 ltac:(lia)) | lia | lia | reflexivity | lia | exact Q0].
           ++ eapply PB.kword32_intro with (A := 0xf684c) (z := 0); [exact (ESL _ 0xf684c ltac:(lia)) | lia | lia | reflexivity | exact Q4].
           ++ eapply PB.kword32_intro with (A := 0xf6850) (z := 2); [exact (ESL _ 0xf6850 ltac:(lia)) | lia | lia | reflexivity | exact Q8].
           ++ eapply CL5.kword64_intro with (A := 0xf6858) (z := 0xf6860); [exact (ESL _ 0xf6858 ltac:(lia)) | lia | lia | reflexivity | exact Q16].
           ++ eapply CL5.kword64_intro with (A := 0xf6860) (z := 0); [exact (ESL _ 0xf6860 ltac:(lia)) | lia | lia | reflexivity | exact Q24].
           ++ eapply CL5.kword64_intro with (A := 0xf6868) (z := 0xa710c); [exact (ESL _ 0xf6868 ltac:(lia)) | lia | lia | unfold PML.ATEXIT_CALL; reflexivity | exact Q32].
           ++ eapply CL5.kword64_intro with (A := 0xf6968) (z := 0x39674); [exact (ESL _ 0xf6968 ltac:(lia)) | lia | lia | unfold PML.AEF_EXIT_GUARD; reflexivity | exact Q288].
           ++ eapply CL5.kword64_intro with (A := 0xf6870) (z := PML.ATEXIT_HANDLER); [exact (ESL _ 0xf6870 ltac:(lia)) | lia | lia | reflexivity | exact Q40].
           ++ eapply CL5.kword64_intro with (A := 0xf6970) (z := PML.OBJ_JSON_CATEGORY); [exact (ESL _ 0xf6970 ltac:(lia)) | lia | lia | reflexivity | exact Q296].
      *
        assert (Hid : id = PML.PC_GUARD_REL).
        { unfold SP.is_call, CALLS1 in Hic. cbn [existsb] in Hic. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in Hic. cbn [orb] in Hic.
          destruct (Z.eqb_spec id PML.PC_GUARD_REL); [assumption | discriminate]. }
        rewrite Hid. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT1.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 1 1) None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G1.CPS GT1.NF E0 M model F1 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G1.CPS GT1.NF F1 eq_refl cut_facts1 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        apply (REL_OK GUARD (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GUARD Xa0 HR (LIT E' GUARD ltac:(unfold GUARD; lia)))|]. split; [unfold GUARD; lia | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GUARD, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GUARD, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' GUARD ltac:(unfold GUARD; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT1.NF E0 F1 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), GUARD, (ELit 2). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 GUARD ltac:(unfold GUARD; lia)), (ELN E0 2 ltac:(lia)). lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := 0xd4df8) (z := 1); [exact (ESL _ 0xd4df8 ltac:(lia)) | lia | lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := 0xd4df9) (z := 1); [exact (ESL _ 0xd4df9 ltac:(lia)) | lia | lia | reflexivity | lia | exact P3].
    +
      intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ ec_facts1 i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X. apply andb_prop in X as [Xec Xst].
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (A10 : PB.uv E' Eb = E) by (rewrite (PB.uv_agree GT1.NF E0 E' Eb HagE eq_refl); exact U10).
      assert (A11 : PB.uv E' (EVar 11) = code) by (rewrite (PB.uv_agree GT1.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
      assert (FB : L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M') by (apply (FRAME F1 M'); [intros rb rlo rlen Hin; exact Hin | exact Hfr]).
      assert (OUT : forall a n, 0x10000 <= a -> a + n <= 0xd4df8 \/ (0xd4dfa <= a /\ a + n <= 0xf6848) -> PB2.out [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] a n).
      { intros a n Ha Hn. split; [lia|]. split; [lia|]. intros j Hj w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      assert (CELL : forall X, In X (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) -> kentry_ok RSEGS E' M' X).
      { intros X0 HX. unfold statics_chk in Xst. rewrite forallb_forall in Xst. exact (PB.has_ok E' M' _ _ HK (Xst X0 HX)). }
      assert (CN : forall n X, nth_error (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) n = Some X -> kentry_ok RSEGS E' M' X)
        by (intros n X0 Hn; exact (CELL X0 (nth_error_In _ _ Hn))).
      assert (ESL : forall z, 0 <= z < 2 ^ 63 -> estart E' (SA (ELit 0) z) = z) by (intros z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
      assert (LIT : forall z, 0 <= z < 2 ^ 64 -> PB.uv E' (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact (ec_exit E' M M' ps0 E code HK Xec A10 A11 Hcode ltac:(lia) ltac:(lia) HdefE Hgr)|]. split.
      * destruct LD as (LD1 & LD2 & LD3).
        split; [intros a Ha; rewrite (FB (Z_to_bv 64 a)); [exact (IMGRO a Ha)|]; rewrite u64_of_Z by (unfold PML.IMG_RO_HI in Ha; lia);
                intros w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn [fst snd]; unfold PML.IMG_RO_HI in Ha; lia|].
        split; [exact (LQF M' FB LQ)|].
        split; [split; [apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact LD1]|]; split; [apply (PB2.u64_fr _ M M' FB); [apply OUT; lia | exact LD2] | apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact LD3]]|].
        split; [split|].
        -- pose proof (PB2.kword8_elim E' M' _ _ 0xd4df8 (CN 0%nat _ eq_refl) (ESL 0xd4df8 ltac:(lia))) as C. rewrite LIT in C by lia. exact C.
        -- pose proof (PB2.kword8_elim E' M' _ _ 0xd4df9 (CN 1%nat _ eq_refl) (ESL 0xd4df9 ltac:(lia))) as C. rewrite LIT in C by lia. exact C.
        -- split; [split; [apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact HC0] | apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact HC1]]|].
           cbn [PML.ls_atexit PML.regJ PML.jreg PML.creg PML.atexit_cells length Z.of_nat Z.add].
           split; [pose proof (PB2.kword8_elim E' M' _ _ 0xf6848 (CN 2%nat _ eq_refl) (ESL 0xf6848 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword32_elim E' M' _ _ 0xf684c (CN 3%nat _ eq_refl) (ESL 0xf684c ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword32_elim E' M' _ _ 0xf6850 (CN 4%nat _ eq_refl) (ESL 0xf6850 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6858 (CN 5%nat _ eq_refl) (ESL 0xf6858 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6860 (CN 6%nat _ eq_refl) (ESL 0xf6860 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6868 (CN 7%nat _ eq_refl) (ESL 0xf6868 ltac:(lia))) as C; rewrite LIT in C by (unfold PML.ATEXIT_CALL; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6968 (CN 8%nat _ eq_refl) (ESL 0xf6968 ltac:(lia))) as C; rewrite LIT in C by (unfold PML.AEF_EXIT_GUARD; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6870 (CN 9%nat _ eq_refl) (ESL 0xf6870 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.ATEXIT_HANDLER; lia); exact C|].
           pose proof (PB2.kword64_elim E' M' _ _ 0xf6970 (CN 10%nat _ eq_refl) (ESL 0xf6970 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.OBJ_JSON_CATEGORY; lia); exact C.
      * unfold ec_chk in Xec. apply andb_prop in Xec as [_ X10]. unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        apply PB.edenot_of_uv. exact A10.
  -
    pose proof HLS as HLS0. destruct HLS as (IMGRO & LQ & LD & (HG0 & HG1) & HCG & HAT).
    unfold PML.cfg. change PML.PC_SET_EC with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := 0xd4df8) (z := 1); [sp_start | lia | lia | reflexivity | lia | exact HG0].
      * sp_unk HdefE. * sp_wr HdefE. * e_range. * e_range.
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
      * sp_disj. * sp_disj.
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ ec_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (A10 : PB.uv E' Eb = E) by (rewrite (PB.uv_agree GT2.NF E0 E' Eb HagE eq_refl); exact U10).
      assert (A11 : PB.uv E' (EVar 11) = code) by (rewrite (PB.uv_agree GT2.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
      assert (FB : L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[X0|[]]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 256, 256); (E, 16)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[X0|[]]]; injection X0 as <- <- <-.
        - exists (sp - 256, 256). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-256)) = sp - 256) by ev_start. assert (El : elenZ E0 (ELit 256) = 256) by ev_len. rewrite Es, El. lia.
        - exists (E, 16). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 10) 0) = E) by ev_start. assert (El : elenZ E0 (ELit 16) = 16) by ev_len. rewrite Es, El. lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact (ec_exit E' M M' ps0 E code HK X A10 A11 Hcode ltac:(lia) ltac:(lia) HdefE Hgr)|]. split.
      * apply (PB2.ls_ok_fr _ M M' FB2 PML.J ltac:(discriminate)); [|exact HLS0].
        split; [lia|]. split; [lia|]. intros a Ha w [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia.
      * unfold ec_chk in X. apply andb_prop in X as [_ X10]. unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        apply PB.edenot_of_uv. exact A10.
  -
    destruct HLS as (IMGRO & LQ & LD & (HG0 & HG1) & (HC0 & HC1) & (HA0 & HA4 & HA8 & HA16 & HA24 & HA32 & HA288 & HA40 & HA296)). cbn [PML.creg] in HA40, HA296. cbn [length Z.of_nat Z.add] in HA8. unfold PML.ATEXIT_CALL in HA32. unfold PML.AEF_EXIT_GUARD in HA288.
    assert (WG : forall Mx : mem, L5.writable RSEGS Mx GUARD 2) by (intros Mx; apply (SP.writable_static RSEGS Mx GUARD 2 guard_wr); unfold GUARD; lia).
    assert (WA : forall Mx : mem, L5.writable RSEGS Mx AX 544) by (intros Mx; apply (SP.writable_static RSEGS Mx AX 544 atexit_wr); unfold AX; lia).
    assert (NF32' : (32 <= GT3.NF)%nat) by (unfold GT3.NF; lia).
    assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
    assert (SCRV : SCR = 256) by reflexivity.
    assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
    assert (CRS_OK : forall rg, In rg CRS -> SGP.region_vars_lt GT3.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a).
    { intros rg [<-|[<-|[<-|[]]]]; (split; [reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot Eb] in Ha; rewrite ?U10 in Ha;
        rewrite ?(u64_of_Z 0) in Ha by lia; rewrite ?(u64_of_Z 2), ?(u64_of_Z 544), ?(u64_of_Z 16) in Ha by lia; unfold GUARD, AX in Ha; rewrite SCRV; lia. }
    unfold PML.cfg. change PML.PC_SET_EC with (CC.cp_pc G3.cp0).
    eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G3.CPS G3.TAGS GT3.NF F3 GT3.ENDS eq_refl NF32' G3.plans G3.tags_ok cut_facts3 rets3 CALLS1 exit_facts3
              fx R M model K E0 G3.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    +
      split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G3.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := 0xd4df8) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HG0].
      * eapply PB2.kword8_intro with (A := 0xd4df9) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HG1].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ GUARD 2); [sp_start | ev_len | unfold GUARD; lia | unfold GUARD; lia | exact (WG M)].
      * eapply PB2.kword8_intro with (A := 0xf6848) (z := 0); [sp_start | lia | lia | reflexivity | lia | exact HA0].
      * eapply PB.kword32_intro with (A := 0xf684c) (z := 0); [sp_start | lia | lia | reflexivity | exact HA4].
      * eapply PB.kword32_intro with (A := 0xf6850) (z := 2); [sp_start | lia | lia | reflexivity | exact HA8].
      * eapply CL5.kword64_intro with (A := 0xf6858) (z := 0xf6860); [sp_start | lia | lia | reflexivity | exact HA16].
      * eapply CL5.kword64_intro with (A := 0xf6860) (z := 0); [sp_start | lia | lia | reflexivity | exact HA24].
      * eapply CL5.kword64_intro with (A := 0xf6868) (z := 0xa710c); [sp_start | lia | lia | reflexivity | exact HA32].
      * eapply CL5.kword64_intro with (A := 0xf6968) (z := 0x39674); [sp_start | lia | lia | reflexivity | exact HA288].
      * eapply CL5.kword64_intro with (A := 0xf6870) (z := PML.ATEXIT_HANDLER); [sp_start | lia | lia | reflexivity | exact HA40].
      * eapply CL5.kword64_intro with (A := 0xf6970) (z := PML.OBJ_CONV_CATEGORY); [sp_start | lia | lia | reflexivity | exact HA296].
      * eapply (SP.kwr_of_writable RSEGS E0 M _ _ AX 544); [sp_start | ev_len | unfold AX; lia | unfold AX; lia | exact (WA M)].
      * sp_unk HdefE. * sp_wr HdefE. * e_range. * e_range.
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
      * sp_disj. * sp_disj.
    +
      intros i c tags k ps0 id Hc Htags Hps Htag Hic.
      assert (IL : CH2.is_leaf G3.CPS G3.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
      pose proof (CH2.leaves_all_sound _ _ _ call_facts3 _ _ _ _ _ IL) as X. unfold call_leaf_chk3 in X. rewrite Hic in X.
      destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
      destruct (CH2.ret_of G3.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G3.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F1) by (left; reflexivity).
      assert (ESL : forall Ex z, 0 <= z < 2 ^ 63 -> estart Ex (SA (ELit 0) z) = z) by (intros Ex z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
      assert (LIT : forall Ex z, 0 <= z < 2 ^ 64 -> PB.uv Ex (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
      assert (ELN : forall Ex z, 0 <= z < 2 ^ 64 -> elenZ Ex (ELit z) = z) by (intros Ex z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; exact Hz).
      assert (A0R : forall e z, a0_is ps0 e = true -> regs_ok E' (CA.ps_reglist ps0) R' -> PB.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Ha HR Hz. unfold a0_is in Ha. apply expr_eqb_eq in Ha. rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota.
        change (ridx 10%bv) with 10%nat. rewrite Ha. apply PB.edenot_of_uv. exact Hz. }
      destruct (Z.eqb_spec id PML.PC_GUARD_ACQ) as [->|N1]; [|destruct (Z.eqb_spec id PML.PC_CXA_ATEXIT) as [->|N2]].
      *
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT3.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 0 2) (Some (ELit 1)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G3.CPS GT3.NF E0 M model F3 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G3.CPS GT3.NF F3 eq_refl cut_facts3 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ 0xd4df8 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL E' 0xd4df8 ltac:(lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword8_elim E' M' _ _ 0xd4df9 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL E' 0xd4df9 ltac:(lia))) as C1. rewrite LIT in C1 by lia.
        apply (ACQ_OK GUARD (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GUARD Xa0 HR (LIT E' GUARD ltac:(unfold GUARD; lia)))|]. split; [unfold GUARD; lia|]. split; [exact C0|]. split; [exact C1 | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P1 & P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GUARD, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GUARD, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' GUARD ltac:(unfold GUARD; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT3.NF E0 F3 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), GUARD, (ELit 2). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 GUARD ltac:(unfold GUARD; lia)), (ELN E0 2 ltac:(lia)). lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := 0xd4df8) (z := 0); [exact (ESL _ 0xd4df8 ltac:(lia)) | lia | lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := 0xd4df9) (z := 2); [exact (ESL _ 0xd4df9 ltac:(lia)) | lia | lia | reflexivity | lia | exact P3].
      *
        apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa1]. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT3.NF SCR CRS 128 0 [(ELit 0, AX, ELit 544)] (SSU.atexit_news2 AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD PML.ATEXIT_HANDLER PML.OBJ_CONV_CATEGORY (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) (Some (ELit 0)) c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G3.CPS GT3.NF E0 M model F3 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    128 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G3.CPS GT3.NF F3 eq_refl cut_facts3 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        rewrite forallb_forall in Xc.
        pose proof (PB2.kword8_elim E' M' _ _ 0xf6848 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) (ESL E' 0xf6848 ltac:(lia))) as C0. rewrite LIT in C0 by lia.
        pose proof (PB2.kword32_elim E' M' _ _ 0xf684c (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) (ESL E' 0xf684c ltac:(lia))) as C4. rewrite LIT in C4 by lia.
        pose proof (PB2.kword32_elim E' M' _ _ 0xf6850 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; left; reflexivity))) (ESL E' 0xf6850 ltac:(lia))) as C8. rewrite LIT in C8 by lia.
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6858 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; right; left; reflexivity))) (ESL E' 0xf6858 ltac:(lia))) as C16. rewrite LIT in C16 by (unfold AX; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6860 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; right; right; left; reflexivity))) (ESL E' 0xf6860 ltac:(lia))) as C24. rewrite LIT in C24 by lia.
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6868 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 5 right; left; reflexivity))) (ESL E' 0xf6868 ltac:(lia))) as C32. rewrite LIT in C32 by (unfold PML.ATEXIT_CALL; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6968 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 6 right; left; reflexivity))) (ESL E' 0xf6968 ltac:(lia))) as C288. rewrite LIT in C288 by (unfold PML.AEF_EXIT_GUARD; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6870 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 7 right; left; reflexivity))) (ESL E' 0xf6870 ltac:(lia))) as C40. rewrite LIT in C40 by (unfold PML.ATEXIT_HANDLER; lia).
        pose proof (PB2.kword64_elim E' M' _ _ 0xf6970 (PB.has_ok E' M' _ _ HK (Xc _ ltac:(do 8 right; left; reflexivity))) (ESL E' 0xf6970 ltac:(lia))) as C296. rewrite LIT in C296 by (unfold PML.OBJ_CONV_CATEGORY; lia).
        assert (Ga1 : getr R' 11%bv = Z_to_bv 64 PML.OBJ_JSON_CATEGORY).
        { apply expr_eqb_eq in Xa1. rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Xa1. reflexivity. }
        apply (ATEXIT2_OK PML.ATEXIT_HANDLER PML.OBJ_JSON_CATEGORY (bv_unsigned (getr R' 12%bv)) (sp + CH2.ci_csp ci) (CC.cp_pc cj) PML.creg fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ PML.ATEXIT_HANDLER Xa0 HR (LIT E' PML.ATEXIT_HANDLER ltac:(unfold PML.ATEXIT_HANDLER; lia)))|]. split; [exact Ga1|].
          split; [unfold PML.a2; symmetry; apply Z_to_bv_bv_unsigned|]. split; [|split; [exact (WA M') | exact (LQF M' (FRAME F3 M' (fun _ _ _ H => H) Gfr) LQ)]].
          split; [exact C0 | split; [exact C4 | split; [exact C8 | split; [exact C16 | split; [exact C24 | split; [exact C32 | split; [exact C288 | split; [exact C40 | exact C296]]]]]]]]. }
        intros fx2 R2 M2 HFP2 (P1 & Q0 & Q4 & Q8 & Q16 & Q24 & Q32 & Q288 & Q40 & Q296 & Q48 & Q304) Hrp2 Hfb2 Hgr2. cbn [PML.creg fst snd] in Q40, Q296. unfold PML.cfg. unfold PML.ATEXIT_CALL in Q32. unfold PML.AEF_EXIT_GUARD in Q288.
        apply (CONT fx2 R2 M2 [] [(AX, 544)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact P1 | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, AX, ELit 544). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' AX ltac:(unfold AX; lia)), (ELN E' 544 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT3.NF E0 F3 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 128 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), AX, (ELit 544). split; [right; right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 AX ltac:(unfold AX; lia)), (ELN E0 544 ltac:(lia)). lia.
        -- cbn [length Z.of_nat Z.add] in Q8. intros X0 HX _. unfold SSU.atexit_news2, AX in HX. cbn [In] in HX.
           destruct HX as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
           ++ eapply PB2.kword8_intro with (A := 0xf6848) (z := 0); [exact (ESL _ 0xf6848 ltac:(lia)) | lia | lia | reflexivity | lia | exact Q0].
           ++ eapply PB.kword32_intro with (A := 0xf684c) (z := 0); [exact (ESL _ 0xf684c ltac:(lia)) | lia | lia | reflexivity | exact Q4].
           ++ eapply PB.kword32_intro with (A := 0xf6850) (z := 3); [exact (ESL _ 0xf6850 ltac:(lia)) | lia | lia | reflexivity | exact Q8].
           ++ eapply CL5.kword64_intro with (A := 0xf6858) (z := 0xf6860); [exact (ESL _ 0xf6858 ltac:(lia)) | lia | lia | reflexivity | exact Q16].
           ++ eapply CL5.kword64_intro with (A := 0xf6860) (z := 0); [exact (ESL _ 0xf6860 ltac:(lia)) | lia | lia | reflexivity | exact Q24].
           ++ eapply CL5.kword64_intro with (A := 0xf6868) (z := 0xa710c); [exact (ESL _ 0xf6868 ltac:(lia)) | lia | lia | unfold PML.ATEXIT_CALL; reflexivity | exact Q32].
           ++ eapply CL5.kword64_intro with (A := 0xf6968) (z := 0x39674); [exact (ESL _ 0xf6968 ltac:(lia)) | lia | lia | unfold PML.AEF_EXIT_GUARD; reflexivity | exact Q288].
           ++ eapply CL5.kword64_intro with (A := 0xf6870) (z := PML.ATEXIT_HANDLER); [exact (ESL _ 0xf6870 ltac:(lia)) | lia | lia | reflexivity | exact Q40].
           ++ eapply CL5.kword64_intro with (A := 0xf6970) (z := PML.OBJ_CONV_CATEGORY); [exact (ESL _ 0xf6970 ltac:(lia)) | lia | lia | reflexivity | exact Q296].
           ++ eapply CL5.kword64_intro with (A := 0xf6878) (z := PML.ATEXIT_HANDLER); [exact (ESL _ 0xf6878 ltac:(lia)) | lia | lia | reflexivity | exact Q48].
           ++ eapply CL5.kword64_intro with (A := 0xf6978) (z := PML.OBJ_JSON_CATEGORY); [exact (ESL _ 0xf6978 ltac:(lia)) | lia | lia | reflexivity | exact Q304].
      *
        assert (Hid : id = PML.PC_GUARD_REL).
        { unfold SP.is_call, CALLS1 in Hic. cbn [existsb] in Hic. rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2) in Hic. cbn [orb] in Hic.
          destruct (Z.eqb_spec id PML.PC_GUARD_REL); [assumption | discriminate]. }
        rewrite Hid. apply andb_prop in X as [X Xa0].
        destruct (SPC.call_chk GT3.NF SCR CRS 0 0 [(ELit 0, GUARD, ELit 2)] (SSU.guard_news (ELit 0) GUARD 1 1) None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
        destruct (SPC.pure_call_ret RSEGS PML.fp_ok G3.CPS GT3.NF E0 M model F3 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) CRS CRS_OK
                    0 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk (SP.SUBF G3.CPS GT3.NF F3 eq_refl cut_facts3 E0 i c Hc) E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
          as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
        apply (REL_OK GUARD (sp + CH2.ci_csp ci) (CC.cp_pc cj) fx' R' M' model K Hh Hl HK0 HFP).
        { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
          split; [exact (A0R _ GUARD Xa0 HR (LIT E' GUARD ltac:(unfold GUARD; lia)))|]. split; [unfold GUARD; lia | exact (WG M')]. }
        intros fx2 R2 M2 HFP2 (P2 & P3) Hrp2 Hfb2 Hgr2. unfold PML.cfg.
        apply (CONT fx2 R2 M2 [] [(GUARD, 2)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
        -- intros w a [<-|[]] Hin. exists (ELit 0, GUARD, ELit 2). split; [left; reflexivity|]. unfold CH2.in_reg, L5.in_rng in *. cbn [fst snd] in Hin.
           rewrite (ESL E' GUARD ltac:(unfold GUARD; lia)), (ELN E' 2 ltac:(lia)). exact Hin.
        -- apply (SPC.hwf_intro GT3.NF E0 F3 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) (CH2.ci_csp ci) 0 _ Gc1 Gs0 Gc2 STKIN ltac:(rewrite SCRV; lia)).
           intros w [<-|[]]. exists (ELit 0), GUARD, (ELit 2). split; [right; right; left; reflexivity|]. cbn [fst snd]. rewrite (ESL E0 GUARD ltac:(unfold GUARD; lia)), (ELN E0 2 ltac:(lia)). lia.
        -- intros X0 [<-|[<-|[]]] _.
           ++ eapply PB2.kword8_intro with (A := 0xd4df8) (z := 1); [exact (ESL _ 0xd4df8 ltac:(lia)) | lia | lia | reflexivity | lia | exact P2].
           ++ eapply PB2.kword8_intro with (A := 0xd4df9) (z := 1); [exact (ESL _ 0xd4df9 ltac:(lia)) | lia | lia | reflexivity | lia | exact P3].
    +
      intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ ec_facts3 i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X. apply andb_prop in X as [Xec Xst].
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (A10 : PB.uv E' Eb = E) by (rewrite (PB.uv_agree GT3.NF E0 E' Eb HagE eq_refl); exact U10).
      assert (A11 : PB.uv E' (EVar 11) = code) by (rewrite (PB.uv_agree GT3.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
      assert (FB : L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M') by (apply (FRAME F3 M'); [intros rb rlo rlen Hin; exact Hin | exact Hfr]).
      assert (OUT : forall a n, 0x10000 <= a -> a + n <= 0xd4df8 \/ (0xd4dfa <= a /\ a + n <= 0xf6848) -> PB2.out [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] a n).
      { intros a n Ha Hn. split; [lia|]. split; [lia|]. intros j Hj w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
      assert (CELL : forall X, In X (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news2 AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD PML.ATEXIT_HANDLER PML.OBJ_CONV_CATEGORY (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) -> kentry_ok RSEGS E' M' X).
      { intros X0 HX. unfold statics_chk3 in Xst. rewrite forallb_forall in Xst. exact (PB.has_ok E' M' _ _ HK (Xst X0 HX)). }
      assert (CN : forall n X, nth_error (SSU.guard_news (ELit 0) GUARD 1 1 ++ SSU.atexit_news2 AX PML.ATEXIT_CALL PML.AEF_EXIT_GUARD PML.ATEXIT_HANDLER PML.OBJ_CONV_CATEGORY (ELit PML.ATEXIT_HANDLER) (ELit PML.OBJ_JSON_CATEGORY)) n = Some X -> kentry_ok RSEGS E' M' X)
        by (intros n X0 Hn; exact (CELL X0 (nth_error_In _ _ Hn))).
      assert (ESL : forall z, 0 <= z < 2 ^ 63 -> estart E' (SA (ELit 0) z) = z) by (intros z Hz; unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; lia).
      assert (LIT : forall z, 0 <= z < 2 ^ 64 -> PB.uv E' (ELit z) = z) by (intros; apply PB2.uv_lit; assumption).
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact (ec_exit E' M M' ps0 E code HK Xec A10 A11 Hcode ltac:(lia) ltac:(lia) HdefE Hgr)|]. split.
      * destruct LD as (LD1 & LD2 & LD3).
        split; [intros a Ha; rewrite (FB (Z_to_bv 64 a)); [exact (IMGRO a Ha)|]; rewrite u64_of_Z by (unfold PML.IMG_RO_HI in Ha; lia);
                intros w [<-|[<-|[<-|[<-|[]]]]]; unfold L5.in_rng; cbn [fst snd]; unfold PML.IMG_RO_HI in Ha; lia|].
        split; [exact (LQF M' FB LQ)|].
        split; [split; [apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact LD1]|]; split; [apply (PB2.u64_fr _ M M' FB); [apply OUT; lia | exact LD2] | apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact LD3]]|].
        split; [split|].
        -- pose proof (PB2.kword8_elim E' M' _ _ 0xd4df8 (CN 0%nat _ eq_refl) (ESL 0xd4df8 ltac:(lia))) as C. rewrite LIT in C by lia. exact C.
        -- pose proof (PB2.kword8_elim E' M' _ _ 0xd4df9 (CN 1%nat _ eq_refl) (ESL 0xd4df9 ltac:(lia))) as C. rewrite LIT in C by lia. exact C.
        -- split; [split; [apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact HC0] | apply (PB2.u8_fr _ M M' FB); [apply OUT; lia | exact HC1]]|].
           cbn [PML.ls_atexit PML.regJ PML.jreg PML.creg PML.atexit_cells length Z.of_nat Z.add fst snd].
           split; [pose proof (PB2.kword8_elim E' M' _ _ 0xf6848 (CN 2%nat _ eq_refl) (ESL 0xf6848 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword32_elim E' M' _ _ 0xf684c (CN 3%nat _ eq_refl) (ESL 0xf684c ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword32_elim E' M' _ _ 0xf6850 (CN 4%nat _ eq_refl) (ESL 0xf6850 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6858 (CN 5%nat _ eq_refl) (ESL 0xf6858 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6860 (CN 6%nat _ eq_refl) (ESL 0xf6860 ltac:(lia))) as C; rewrite LIT in C by lia; exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6868 (CN 7%nat _ eq_refl) (ESL 0xf6868 ltac:(lia))) as C; rewrite LIT in C by (unfold PML.ATEXIT_CALL; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6968 (CN 8%nat _ eq_refl) (ESL 0xf6968 ltac:(lia))) as C; rewrite LIT in C by (unfold PML.AEF_EXIT_GUARD; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6870 (CN 9%nat _ eq_refl) (ESL 0xf6870 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.ATEXIT_HANDLER; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6970 (CN 10%nat _ eq_refl) (ESL 0xf6970 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.OBJ_CONV_CATEGORY; lia); exact C|].
           split; [pose proof (PB2.kword64_elim E' M' _ _ 0xf6878 (CN 11%nat _ eq_refl) (ESL 0xf6878 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.ATEXIT_HANDLER; lia); exact C|].
           pose proof (PB2.kword64_elim E' M' _ _ 0xf6978 (CN 12%nat _ eq_refl) (ESL 0xf6978 ltac:(lia))) as C; unfold AX in C; rewrite LIT in C by (unfold PML.OBJ_JSON_CATEGORY; lia); exact C.
      * unfold ec_chk in Xec. apply andb_prop in Xec as [_ X10]. unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        apply PB.edenot_of_uv. exact A10.
  -
    pose proof HLS as HLS0. destruct HLS as (IMGRO & LQ & LD & (HG0 & HG1) & HCG & HAT).
    unfold PML.cfg. change PML.PC_SET_EC with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := 0xd4df8) (z := 1); [sp_start | lia | lia | reflexivity | lia | exact HG0].
      * sp_unk HdefE. * sp_wr HdefE. * e_range. * e_range.
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
      * sp_disj. * sp_disj.
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ ec_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (A10 : PB.uv E' Eb = E) by (rewrite (PB.uv_agree GT2.NF E0 E' Eb HagE eq_refl); exact U10).
      assert (A11 : PB.uv E' (EVar 11) = code) by (rewrite (PB.uv_agree GT2.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
      assert (FB : L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[X0|[]]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 256, 256); (E, 16)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[X0|[]]]; injection X0 as <- <- <-.
        - exists (sp - 256, 256). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-256)) = sp - 256) by ev_start. assert (El : elenZ E0 (ELit 256) = 256) by ev_len. rewrite Es, El. lia.
        - exists (E, 16). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 10) 0) = E) by ev_start. assert (El : elenZ E0 (ELit 16) = 16) by ev_len. rewrite Es, El. lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact (ec_exit E' M M' ps0 E code HK X A10 A11 Hcode ltac:(lia) ltac:(lia) HdefE Hgr)|]. split.
      * apply (PB2.ls_ok_fr _ M M' FB2 PML.JC ltac:(discriminate)); [|exact HLS0].
        split; [lia|]. split; [lia|]. intros a Ha w [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia.
      * unfold ec_chk in X. apply andb_prop in X as [_ X10]. unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        apply PB.edenot_of_uv. exact A10.
  -
    pose proof HLS as HLS0. destruct HLS as (IMGRO & LQ & LD & (HG0 & HG1) & HCG & HAT).
    unfold PML.cfg. change PML.PC_SET_EC with (CC.cp_pc G2.cp0).
    eapply (SP.pure_leaf_sound RSEGS PML.fp_ok FPM G2.CPS G2.TAGS GT2.NF F2 GT2.ENDS eq_refl ltac:(unfold GT2.NF; lia) G2.plans G2.tags_ok cut_facts2 exit_facts2 rets2
              fx R M model K E0 G2.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
    + split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G2.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      * eapply PB2.kword8_intro with (A := 0xd4df8) (z := 1); [sp_start | lia | lia | reflexivity | lia | exact HG0].
      * sp_unk HdefE. * sp_wr HdefE. * e_range. * e_range.
      * sp_unk S5. * sp_wr S5. * e_range. * e_align S1.
      * cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
      * sp_disj. * sp_disj.
    + intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag HFP HagE HLF Hfr Hgr Hrp.
      pose proof (CC.others_all_sound _ _ _ ec_facts2 i c tags k ps0 id Hc Htags Hps Htag) as X.
      assert (HK : know_ok RSEGS E' M' (SR.ps_cells ps0)) by (unfold know_ok; apply Forall_forall; exact (CC.lf_cells _ _ _ _ _ _ _ HLF)).
      assert (A10 : PB.uv E' Eb = E) by (rewrite (PB.uv_agree GT2.NF E0 E' Eb HagE eq_refl); exact U10).
      assert (A11 : PB.uv E' (EVar 11) = code) by (rewrite (PB.uv_agree GT2.NF E0 E' (EVar 11) HagE eq_refl); exact U11).
      assert (FB : L5.frame_but [(sp - 256, 256); (E, 16); (0xd4df8, 2); (0xf6848, 544)] M M').
      { apply (FRAME F2 M'); [|exact Hfr]. intros rb rlo rlen Hin. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin. unfold F1. cbn [G1.cp0 CC.cp_F In].
        destruct Hin as [X0|[X0|[]]]; rewrite <- X0; tauto. }
      assert (FB2 : L5.frame_but [(sp - 256, 256); (E, 16)] M M').
      { apply (SP.frame_but_of_outside E0 F2 _ M M'); [|exact Hfr]. intros rb rlo rlen Hin. right. unfold F2 in Hin. cbn [G2.cp0 CC.cp_F In] in Hin.
        destruct Hin as [X0|[X0|[]]]; injection X0 as <- <- <-.
        - exists (sp - 256, 256). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-256)) = sp - 256) by ev_start. assert (El : elenZ E0 (ELit 256) = 256) by ev_len. rewrite Es, El. lia.
        - exists (E, 16). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 10) 0) = E) by ev_start. assert (El : elenZ E0 (ELit 16) = 16) by ev_len. rewrite Es, El. lia. }
      apply (Hcont fx' R' M' HFP); [| exact Hrp | exact FB | exact Hgr].
      split; [exact (ec_exit E' M M' ps0 E code HK X A10 A11 Hcode ltac:(lia) ltac:(lia) HdefE Hgr)|]. split.
      * apply (PB2.ls_ok_fr _ M M' FB2 PML.CJ ltac:(discriminate)); [|exact HLS0].
        split; [lia|]. split; [lia|]. intros a Ha w [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia.
      * unfold ec_chk in X. apply andb_prop in X as [_ X10]. unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl).
        apply PB.edenot_of_uv. exact A10.
Qed.
End S.
End SetEcProof.

