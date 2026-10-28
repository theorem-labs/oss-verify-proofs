(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HEmpK LbB_HXmpD LbB_HXmpI LbB_HXmpI2 LbB_HXmpI3 LbB_HXmpI4.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_IDX : Z := 0xfba64.
Definition srX : list expr :=
  srs sr_id [(9%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (22%bv, EVar 33); (23%bv, shEe (EAlu ALU_ADD (EVar 32) (ELit 8)))].
Definition SCR_X2 := SCR [false] [EVar 34] [].
Definition SCR_X3 := SCR [true; false] [EVar 34] [].
Definition SCR_X4 := SCR [true; true] [EVar 34] [].

Lemma land_oe : forall x, 0 <= x -> Z.land (2 * x + 1) (2 * x) = 2 * x.
Proof.
  intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 0) as [->|Hne].
  - rewrite Z.testbit_even_0. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia. apply Bool.andb_diag.
Qed.

Lemma bseq_oddX : forall b, In b BSEQ -> b <> 0 -> b <> 2 -> exists x, 1 <= x /\ b = 2 * x + 1.
Proof.
  intros b Hin H0 H2. exists (b / 2). pose proof (Z.div_mod b 2 ltac:(lia)) as D.
  assert (Hm : b mod 2 = 1 /\ 3 <= b).
  { unfold BSEQ in Hin. repeat (destruct Hin as [<-|Hin]; [first [exfalso; lia | split; [reflexivity | lia]] |]). destruct Hin. }
  lia.
Qed.

Lemma land_bseqX : forall b, In b BSEQ -> b <> 0 -> b <> 2 -> Z.land b (b + -1) = b - 1 /\ 3 <= b.
Proof.
  intros b Hin H0 H2. destruct (bseq_oddX b Hin H0 H2) as (x & Hx & ->).
  replace (2 * x + 1 + -1) with (2 * x) by lia. rewrite land_oe by lia. split; lia.
Qed.

Section EmpX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).

  Lemma stage_idx : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 : word)
      (errv' : word) (LB' LBm' : list block) (p bl2 bc2 : Z) (ents2 : list (Z * (Z * Z))) (rehashed : bool),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10 y11 y12 y13 y14
                             y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                             (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24)))
                             s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_IDX) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ents2 rehashed ->
    as_SR H QIx (mkCfg msF mo).
  Proof using All.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y28 y29 y30 y31 errv' LB' LBm' p bl2 bc2 ents2 rehashed
      VIS FRZ KR IP.
    pose proof IP as IP0.
    destruct IP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & LFO & U & SH & PERM & BC0 & LD & KR32
                     & AD & WR & P0 & P1 & P16 & PO & PA & NC & ADP & RHF & RHT & RH & PE & PM & OWN & XP & RF & AC & S0 & AL).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (LbB_HFind.BSEQ_boundA bc2 (u_bseq U)) as BCR.
    destruct (u_hdr U) as [_ Cbc _ _ _ _].
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    unfold spf in VIS.
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) y10 y11 y12 y13 y14
                  y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) y20 (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key)
                  (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 p) (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24)))
                  s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc2]).
    assert (HR : regs_ok E srX R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; rewrite w_add by lia; reflexivity]|].
      apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity]|].
      apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [intros X; discriminate X|]. subst R. unfold shEe. evs.
      transitivity (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)); [reflexivity|].
      rewrite (w_add obj 8) by lia. rewrite LbB_HXmpS.srl3_val by lia.
      rewrite w_add by (pose proof (Z.div_pos (obj + 8) 8); pose proof (Z.div_le_upper_bound (obj + 8) 8 (2 ^ 47)); lia). reflexivity. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    assert (RUN : exists R', CatSim.msteps asegs (MS R F (Z_to_bv 64 E_IDX) fc None m (seg_rom asegs))
                                             (MS R' F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs))
              /\ R' = mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (getr R' 9) (Z_to_bv 64 p) (getr R' 11)
                          (getr R' 12) y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc2)
                          (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (getr R' 23) (Z_to_bv 64 (hmod key bc2))
                          (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31).
    { destruct (Z.eqb_spec bc2 2) as [B2 | B2]; [|destruct (Z.ltb_spec key bc2) as [KL | KL]].
      - assert (HK : know_ok asegs E m (kn_fix 20 [E_INS] SCR_X2 E_IDX srX [] 50)) by (kn_eval; know_tac).
        xrun_at (PropExec.mkFP F fc) asegs R E_IDX m (seg_rom asegs) HR HK 40%nat [E_INS] SCR_X2 50%N.
        { clear - E Cbc GZO Ho0 Ho1 BCR B2 KR32. split_scs; try sc_auto1; try sc_shdj; try sc_dj;
            cbn [sc_denot]; evs; rewrite B2; vm_compute; reflexivity. }
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        rreg HR' 10%bv G10. rreg HR' 20%bv G20. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
        assert (G10' : getr R' 10 = Z_to_bv 64 p) by (rewrite G10, HR0; reflexivity).
        assert (G24' : getr R' 24 = Z_to_bv 64 (hmod key bc2)).
        { rewrite G24, B2. rewrite w_addm, w_and by lia. unfold hmod. replace (2 + -1) with 1 by lia.
          rewrite Z.land_comm, LbB_HXmpS.land_1S. reflexivity. }
        rewrite G10', G20, G22, G24' in HRe. exists R'. split; [exact Hms | exact HRe].
      - destruct (land_bseqX bc2 (u_bseq U) BC0 B2) as [LND B3].
        assert (HK : know_ok asegs E m (kn_fix 20 [E_INS] SCR_X3 E_IDX srX [] 50)) by (kn_eval; know_tac).
        xrun_at (PropExec.mkFP F fc) asegs R E_IDX m (seg_rom asegs) HR HK 40%nat [E_INS] SCR_X3 50%N.
        { clear - E Cbc GZO Ho0 Ho1 BCR LND B3 KL KR32. split_scs; try sc_auto1; try sc_shdj; try sc_dj;
            cbn [sc_denot]; evs; rewrite w_addm, w_and by lia; rewrite LND; rewrite br_ne by lia; bool_lia. }
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        rreg HR' 10%bv G10. rreg HR' 20%bv G20. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
        assert (G10' : getr R' 10 = Z_to_bv 64 p) by (rewrite G10, HR0; reflexivity).
        assert (G24' : getr R' 24 = Z_to_bv 64 (hmod key bc2)) by (rewrite G24; unfold hmod; rewrite Z.mod_small by lia; reflexivity).
        rewrite G10', G20, G22, G24' in HRe. exists R'. split; [exact Hms | exact HRe].
      - destruct (land_bseqX bc2 (u_bseq U) BC0 B2) as [LND B3].
        assert (HK : know_ok asegs E m (kn_fix 20 [E_INS] SCR_X4 E_IDX srX [] 50)) by (kn_eval; know_tac).
        xrun_at (PropExec.mkFP F fc) asegs R E_IDX m (seg_rom asegs) HR HK 40%nat [E_INS] SCR_X4 50%N.
        { clear - E Cbc GZO Ho0 Ho1 BCR LND B3 KL KR32. split_scs; try sc_auto1; try sc_shdj; try sc_dj;
            cbn [sc_denot]; evs; rewrite w_addm, w_and by lia; rewrite LND; rewrite br_ne by lia; bool_lia. }
        readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
        rreg HR' 10%bv G10. rreg HR' 20%bv G20. rreg HR' 22%bv G22. rreg HR' 24%bv G24.
        assert (G10' : getr R' 10 = Z_to_bv 64 p) by (rewrite G10, HR0; reflexivity).
        assert (G24' : getr R' 24 = Z_to_bv 64 (hmod key bc2)) by (rewrite G24; unfold hmod; rewrite w_remu by lia; reflexivity).
        rewrite G10', G20, G22, G24' in HRe. exists R'. split; [exact Hms | exact HRe]. }
    destruct RUN as (R' & Hms & HRe).
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_ins H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s msF1 mo1 m F fc) with (errv' := errv') (LB' := LB') (LBm' := LBm') (p := p) (bl2 := bl2) (bc2 := bc2)
            (ents2 := ents2) (rehashed := rehashed);
      [unfold ISTATE; exact VIS1 | exact FRZ | exact KR1 |].
    destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
  Qed.
End EmpX.
