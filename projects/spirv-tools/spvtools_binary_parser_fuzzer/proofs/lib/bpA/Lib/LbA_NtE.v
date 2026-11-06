(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel HFpu HCommon.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsWalk CXXRep RtA_Iface LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_Own LbA_MILB
  LbA_PrsStmt LbA_ContStmt LbA_HEmpStmt LbA_HKit LbA_HStKit LbA_VecT LbA_NtStmt LbA_NtK LbA_NtRK LbA_NtD LbA_NtI LbA_NtI4
  LbA_NtRL LbA_NtRE LbA_NtRB LbA_NtF LbA_NtG LbA_NtNd LbA_NtS.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_HFind LbA_TopKit LbA_HEmpD LbA_HEmpI LbA_HEmpS LbA_HEmpNd LbA_RGl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_DSP : Z := 0xf33fc.

Definition srEN : list expr := srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (24%bv, ELit SHBASE)].
Definition KN_EN : list kentry :=
  [KWord (SA (EVar 32) 384) 8 (EAlu ALU_ADD (EVar 33) (ELit 8)); KWord (SA (EVar 32) 440) 8 (EVar 34); KWord (SA (EVar 32) 448) 8 (EVar 33);
   KWr (SA (EVar 32) 832) (ELit 16); KWr (SA (EVar 32) 1032) (ELit 8);
   KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 1040); KRange (EVar 33) 7233536 (2 ^ 47 - 40); KRange (EVar 34) 0 (2 ^ 47 - 8)].
Definition SCR_EN := SCR [] [EVar 35; EVar 36] [].

Definition srD : list expr := srs sr_id [(23%bv, EVar 34); (16%bv, EVar 33); (2%bv, EVar 35); (9%bv, EVar 35)].
Definition KN_D : list kentry :=
  [KWord (SA (EVar 35) 264) 8 (ELit 0x01010101); KWord (SA (EVar 35) 272) 8 (ELit 0x0f0f0f0f);
   KWord (SA (EVar 35) 280) 8 (ELit 0x33333333); KWord (SA (EVar 35) 288) 8 (ELit 0x55555555); KRange (EVar 35) (2 ^ 45) (2 ^ 47 - 1040)].

Definition popcD : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec ASEGS 100 true [0xf3464] (SCR [false] [] []) (SS E_DSP srD [] KN_D 50) [] in
     sr_get (s_regs ss) 12%bv).
Definition popcwD (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcD.
Lemma popcD_env : forall E, edenot E popcD = popcwD (ev E 34).
Proof. intros E. unfold popcwD, popcD. cbn [edenot ev]. reflexivity. Qed.
Ltac vm_popcD :=
  match goal with |- context [bv_unsigned (popcwD ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcwD w)) in
    replace (bv_unsigned (popcwD w)) with v by (vm_compute; reflexivity) end.
Lemma popcwD_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcwD (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcwD (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popcD; reflexivity]
            | right; split; [lia | vm_popcD; lia] ] |]).
  destruct Hin.
Qed.

Definition non_dsp : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition aonlyD (R R' : bvmap 5 word) : Prop := forall r, In r non_dsp -> getr R' r = getr R r.
Definition SCR_D0 := SCR [true] [] [].
Definition SCR_D2 := SCR [false; false] [] [].
Definition SCR_Dlt := SCR [false; true; true] [] [].
Definition SCR_Dge := SCR [false; true; false] [] [].

Section Dsp.
  Context {fx : PropExec.FPState}.
  Context {AC : AllocCeiling}.
  Variable rom : word -> option byte.
  Variables (M : mem) (S1 key bc : Z).
  #[local] Abbreviation st R pc := (@PropExec.mkst fx R (Z_to_bv 64 pc) M rom).
  Hypothesis R264 : rw_cells asegs M (S1 + 264) [C8 (Z_to_bv 64 0x01010101); C8 (Z_to_bv 64 0x0f0f0f0f); C8 (Z_to_bv 64 0x33333333);
                                                C8 (Z_to_bv 64 0x55555555)].
  Hypothesis SPL : 2 ^ 45 <= S1.
  Hypothesis SPH : S1 + 1040 <= 2 ^ 47.

  Ltac runD R scr :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in let Hpc := fresh "Hpc" in
    pose (E := Eseed R [Z_to_bv 64 0; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 S1]);
    assert (HR : regs_ok E srD R) by
      (apply regs_ok_srs; [apply regs_ok_seed|];
       repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; assumption] |]); apply Forall_nil);
    assert (HK : know_ok ASEGS E M KN_D) by
      (unfold know_ok;
       apply Forall_cons; [kword_cell R264 0%nat (C8 (Z_to_bv 64 0x01010101)) |];
       apply Forall_cons; [kword_cell R264 8%nat (C8 (Z_to_bv 64 0x0f0f0f0f)) |];
       apply Forall_cons; [kword_cell R264 16%nat (C8 (Z_to_bv 64 0x33333333)) |];
       apply Forall_cons; [kword_cell R264 24%nat (C8 (Z_to_bv 64 0x55555555)) |];
       apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]);
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popcD) = b ->
                  sc_denot ASEGS M E (SCBr b BC_LTU (ELit 1) popcD)) by (intros b Hb; exact Hb);
    xrun HR HK 60%nat [E_BB; E_NF] scr 50%N;
    [ split_scs; try sc_auto1;
      try (apply Hpc; rewrite popcD_env; evs; rewrite branch_ltu_lit_l by lia; bool_lia);
      try (cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia; bool_lia)
    | ].

  Lemma dsp_z : forall R, getr R 23%bv = Z_to_bv 64 bc -> getr R 16%bv = Z_to_bv 64 key -> getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 ->
    bc = 0 ->
    exists R', CatSim.msteps ASEGS (st R E_DSP) (st R' E_NF) /\ aonlyD R R'.
  Proof.
    intros R H23 H16 H2 H9 Hbc. runD R SCR_D0.
    exists R'. split; [exact Hms|]. intros r Hr. refine (LbA_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr). vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma dsp_nz : forall R, In bc BSEQ -> bc <> 0 -> 0 <= key < 2 ^ 32 ->
    getr R 23%bv = Z_to_bv 64 bc -> getr R 16%bv = Z_to_bv 64 key -> getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 ->
    exists R' pw, CatSim.msteps ASEGS (st R E_DSP) (st R' E_BB) /\ aonlyD R R' /\ getr R' 26%bv = Z_to_bv 64 (hmod key bc)
      /\ getr R' 12%bv = Z_to_bv 64 pw /\ 0 <= pw < 2 ^ 64 /\ (bc <> 2 -> 2 <= pw) /\ (bc = 2 -> pw < 2).
  Proof.
    intros R Hin Hbc Hk H23 H16 H2 H9. pose proof (LbA_HFind.BSEQ_boundA bc Hin) as Hbcr.
    pose proof (bv_unsigned_in_range 64 (popcwD (Z_to_bv 64 bc))) as PWR. change (bv_modulus 64) with (2 ^ 64) in PWR.
    destruct (popcwD_cases bc Hin Hbc) as [[Hbc2 Hp1]|[Hbc2 Hp2]].
    - runD R SCR_D2.
      assert (P11 : getr R' 12%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 12%bv) (popcD_env E)).
      rreg HR' 26%bv G27.
      exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
      split; [intros r Hr; refine (LbA_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
      split; [rewrite G27; rewrite w_addm, w_and by lia; subst bc; unfold hmod; change (2 + -1) with (Z.ones 1); rewrite Z.land_comm, Z.land_ones by lia; reflexivity|].
      split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
    - destruct (Z.lt_ge_cases key bc) as [Hlt|Hge].
      + runD R SCR_Dlt.
        assert (P11 : getr R' 12%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 12%bv) (popcD_env E)).
        rreg HR' 26%bv G27.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbA_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G27; unfold hmod; rewrite Z.mod_small by lia; reflexivity|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
      + runD R SCR_Dge.
        assert (P11 : getr R' 12%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 12%bv) (popcD_env E)).
        rreg HR' 26%bv G27.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbA_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G27; unfold hmod; apply LbA_HFind.remuw_valA; lia|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
  Qed.
End Dsp.

Section NtE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Tactic Notation "rq" constr(AO) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO (r : reg) ltac:(inb)) as Q; rewrite HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.
  Tactic Notation "rq2" constr(AO3) constr(AO2) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO3 (r : reg) ltac:(inb)) as Q; rewrite (AO2 (r : reg) ltac:(inb)), HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.

  Theorem nt_specA : nt_stmt H.
  Proof.
    intros ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LB0 LBm LF CH
      S1 obj bl bc keyp key v784 ents lo B shi errv j816 j824 j832 j840 j880 j904 j1032
      VIS FRZ U SH PE PM ADH WRH LFO OCE OBL FK EK K0 KCE K4 KR32 RS V64 W816 W880 W904 W1032 ZLEN BCL RH KR AL0 RSM RCN RLG RICM
      CHN TRK CHH RA SPB BR SP16 ST ACL LOR ERR MI TPV AC RF S0 SHI OWN.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    assert (LOS : lo <= S1) by (clear - LOR'; lia).
    assert (SPH : S1 + 1040 <= 2 ^ 47) by (destruct S0 as (g & _ & Hg & _); unfold AAPP_HI in Hg; clear - Hg SHI; lia).
    assert (SPL : 2 ^ 45 <= S1) by (clear - ACF1 ACL LOR'; lia).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbA_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (apply LbA_HEmpI.gzA; [exact ADH | reflexivity]).
    pose proof (LbA_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    destruct EK as (EK1 & EK2 & EK3).
    pose proof RS as RS0. destruct RS0 as (R264 & R312 & R336 & R384 & R400 & R440 & R448 & R784 & R976).
    remember (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                  (Z_to_bv 64 SHBASE) s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).

    assert (CK : cellw ASEGS m keyp 4 key) by (split; [cbn; lia | exact FK]).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E srEN R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_b : sc_denot asegs m E (SCReadBase (SA (EVar 33) 8) 8 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (Hrd_k : sc_denot asegs m E (SCReadBase (SA (EVar 34) 0) 4 false (EVar 36))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ CK); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_DSP] SCR_EN NT_ENTRY srEN KN_EN 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 8))));
          [ exact R384 | reflexivity | reflexivity | lia
          | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [cbytes]; evs; rewrite w_add by lia; reflexivity ]. }
      apply Forall_cons; [kword_cell R440 0%nat (C8 (Z_to_bv 64 keyp))|].
      apply Forall_cons; [kword_cell R448 0%nat (C8 (Z_to_bv 64 obj))|].
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; clear - ACL LOS; cbn [a_off a_base]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off a_base]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; clear - ACL LOS; cbn [a_off a_base]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off a_base]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - K0 KCE ACF2; lia|].
      clear - GZO Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R NT_ENTRY m (seg_rom asegs) HR HK 30%nat [E_DSP] SCR_EN 50%N.
    { clear - E Hrd_b Hrd_k K0 KCE ACL LOS OCE Ho0 Ho1 SPL SPH.
      split_scs; first [exact Hrd_b | exact Hrd_k | sc_dj | sc_auto1]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    set (W1 := [(S1 + 1032, S1 + 1040); (S1 + 840, S1 + 848); (S1 + 832, S1 + 840)]).
    assert (MU1 : munch W1 m M1).
    { subst M1 W1. apply munch_mem_denot; [exact Hlf|]. clear - E SPL SPH Ho0 Ho1.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 1040)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WROK : forall l h, S1 <= l -> h <= S1 + 1040 -> l <= h ->
                   aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)).
    { intros l h Hl Hh Hlh. assert (Xl : aceil <= l) by (clear - ACL LOS Hl; lia).
      destruct (stack_window_ok H LB LF l h Xl FB2) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. left. cbn. unfold AHI_LO. clear - SPL Hl. lia. }
    assert (FW : Forall (fun iv => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) W1).
    { subst W1. apply Forall_cons; [apply WROK; lia|]. apply Forall_cons; [apply WROK; lia|]. apply Forall_cons; [apply WROK; lia | apply Forall_nil]. }
    assert (F1 : Forall (aclient_write_ok H LB) W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj2 (proj2 (proj2 X)))).
    destruct (client_frame H HH s LB LF B W1 m M1 RH RF AC RA MU1 WM1 F1 F2 F3) as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact F4]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m M1).
    { eapply (xpres_munch_mixed H HH s LB LB0 LBm S1 (nt_X S1 obj) W1 m m M1); [apply xpres_refl | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      subst W1. repeat (apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs nt_X Datatypes.fst Datatypes.snd] in *; lia|]). apply Forall_nil. }
    assert (AG1 : forall a k, 0 <= a -> 0 <= k -> a + k <= S1 + 832 -> agree_on m M1 a k).
    { intros a k Ha Hk Hak. eapply agree_of_munch; [exact MU1 | | lia | clear - Hak SPH; lia]. intros z Hz. subst W1. cbn. clear - Hz Hak. lia. }
    assert (DSH1 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W1 (sh A) (nsh k)).
    { intros A k HA Hk HAk. subst W1. apply LbA_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      pose proof (sh_nsh_high A k HA Hk ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      unfold ALOWSH_LO, AHI_LO. repeat (apply Forall_cons; [cbn [fst snd]; clear - SPL; lia |]). apply Forall_nil. }

    assert (WRS : forall o k, 0 <= o -> o + k <= 1040 -> 0 <= k -> wr_at asegs m (S1 + o) k).
    { intros o k Ho Hk Hk0. eapply LbA_HEmpD.wr_at_subE; [exact (wr_at_of_stk _ _ _ _ ST) | clear - LOS Ho; lia | clear - Hk; lia | exact Hk0]. }
    assert (X816 : rw_cells asegs m (S1 + 816) ([C8 j816; C8 j824] ++ [C8 j832; C8 j840])) by exact W816.
    apply rw_cells_app in X816 as [X816a _].
    assert (W816a : rw_cells asegs M1 (S1 + 816) [C8 j816; C8 j824]) by (eapply rw_cells_transport; [exact X816a | exact MU1 | exact WM1 | subst W1; cbn; lia]).
    assert (W832a : rw_cells asegs M1 (S1 + 832) [C8 s9]).
    { subst M1. rwc_newT Hlf (WRS 832 8 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; rewrite HR0; reflexivity). }
    assert (W840a : rw_cells asegs M1 (S1 + 840) [C8 s7]).
    { subst M1. rwc_newT Hlf (WRS 840 8 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; rewrite HR0; reflexivity). }
    assert (W1032a' : rw_cells asegs M1 (S1 + 1032) [C8 (Z_to_bv 64 ((obj + 8) / 8 + SHBASE))]).
    { subst M1. rwc_newT Hlf (WRS 1032 8 ltac:(lia) ltac:(lia) ltac:(lia))
        ltac:(evs; rewrite (w_add obj 8) by lia; rewrite (LbA_NtD.sh_word (obj + 8)) by lia; reflexivity). }
    assert (W1032a : rw_cells asegs M1 (S1 + 1032) [C8 (Z_to_bv 64 (sh (obj + 8)))]).
    { replace (sh (obj + 8)) with ((obj + 8) / 8 + SHBASE) by (unfold sh; rewrite ASHADOW_BASE_val; unfold SHBASE; lia). exact W1032a'. }
    assert (WS1 : WSLOTS s7 s9 S1 obj M1 j816 j824 j880 j904).
    { unfold WSLOTS. split; [|split; [|split]].
      - change [C8 j816; C8 j824; C8 s9; C8 s7] with ([C8 j816; C8 j824] ++ [C8 s9] ++ [C8 s7]).
        apply rw_cells_app. split; [exact W816a|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
        apply rw_cells_app. split; [eapply rw_cells_addr; [exact W832a | lia]|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
        eapply rw_cells_addr; [exact W840a | lia].
      - eapply rw_cells_transport; [exact W880 | exact MU1 | exact WM1 | subst W1; cbn; lia].
      - eapply rw_cells_transport; [exact W904 | exact MU1 | exact WM1 | subst W1; cbn; lia].
      - exact W1032a. }
    assert (RS1 : nt_slots M1 S1 obj keyp v784).
    { unfold nt_slots. repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | subst W1; cbn; lia]). }
    pose proof RS1 as RS1'. destruct RS1' as (R264a & _ & _ & _ & _ & _ & R448a & R784a & R976a).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { assert (EA : errno_addr tp = 7093876) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
      rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | subst W1; cbn; clear - SPL; lia]. }
    assert (U1 : umapx MI_A 32 (nval32 ASEGS) (lbl LB) M1 obj bl bc ents).
    { eapply (umapx_agree ASEGS LY_A MI_A 32 _ (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) (lbl LB) (lbl LB) m M1); [exact U | | intros; assumption].
      intros a Ha.
      assert (AGa : 0 <= aceil) by (clear - ACF1; lia). assert (AGb : 0 + aceil <= S1 + 832) by (clear - ACL LOS; lia).
      pose proof (AG1 0 aceil (Z.le_refl 0) AGa AGb) as AG.
      assert (Ha' : 0 <= a < aceil).
      { destruct Ha as [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | |].
        - pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
          destruct (lbl_in_inv LBm bl (8 * bc) (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (_ & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC. lia.
        - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
          destruct (lbl_in_inv LBm q 32 (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (Q0 & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC, Q0. cbn in Hqa. clear - QC Q0 Hqa. lia. }
      pose proof (AG a ltac:(lia)) as X. rewrite Z.add_0_l in X. exact X. }
    assert (SH1 : umap_sh M1 32 (bl, bc, ents)).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *. split.
      - intros Hbc. pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH1; lia].
      - intros q k v Hin. destruct (ent_facts _ _ _ _ _ _ _ U Hin) as (E0 & E1 & _). cbn in E0, E1.
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU1 | exact WM1 | apply DSH1; lia]. }
    assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH1; lia]).
    assert (WRH1 : wr_at asegs M1 obj 40) by exact (wr_at_wmono _ _ _ _ WRH WM1).
    assert (FK1 : fldA M1 keyp 4 key).
    { unfold fldA in FK |- *. eapply (CRep.fld_agree ASEGS); [lia | cbn; lia | exact FK |].
      intros a Ha. unfold zwin in Ha. cbn [Z.of_nat] in Ha. pose proof (AG1 keyp 4 ltac:(lia) ltac:(lia) ltac:(clear - KCE ACL LOS; lia) (a - keyp) ltac:(lia)) as X.
      replace (keyp + (a - keyp)) with a in X by lia. exact X. }
    assert (OWN1 : lb_own LBm M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    assert (CHN1 : as_chain H M1 (bv_unsigned s0) CH).
    { eapply (chain_keep H HH m M1 _ CH S1); [exact CHN | exact CHH |].
      intros a Ha. apply MU1. rewrite u64_of_Z by lia. subst W1. cbn. lia. }
    assert (NP1 : forall mo1, as_MPRES H mo mo1 ->
              NPRE H tp s0 s7 s9 S1 s LB0 LF obj key keyp v784 ents bl bc lo B shi m mo CH s mo1 M1 errv LB LBm j816 j824 j880 j904).
    { intros mo1 MP1. unfold NPRE.
      split; [exact MP1|]. split; [exact WS1|]. split; [exact RS1|]. split; [exact SPL|]. split; [exact SPH|]. split; [exact V64|].
      split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|].
      split; [exact U1|]. split; [exact SH1|]. split; [exact ADH1|]. split; [exact WRH1|].
      split; [exact FK1|]. split; [exact (conj EK1 (conj EK2 EK3))|].
      split; [exact RH1|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN1|]. split; [exact XP1|].
      split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. split; [apply Z.le_ge; apply Z.le_refl|]. split; [exact AL0|].
      split; [exact RSM|]. split; [exact RCN|]. split; [exact RLG|]. split; [exact RICM|]. exact CHN1. }

    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 15%bv G15. rreg HR' 16%bv G16. rreg HR' 23%bv G23.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 24%bv G24.
    change (getr R' 24 = Z_to_bv 64 SHBASE) in G24.
    rewrite (HWord.w_srl obj 3) in G15 by lia. change (obj / 2 ^ 3) with (obj / 8) in G15.
    rewrite G10, G11, G15, G16, G23, G2, G9, G24 in HRe. clear G10 G11 G15 G16 G23 G2 G9 G24.

    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbcn].
    - destruct (@dsp_z (PropExec.mkFP F fc) (seg_rom asegs) M1 S1 key bc R264a SPL SPH R' ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity)
                  ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) Hbc0) as (R2 & Hms2 & AO2).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.
      eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms12 |].
      intros msF1 mo1 KR1 MP1 VIS1.
      rq AO2 HRe 2%bv Q2. rq AO2 HRe 3%bv Q3. rq AO2 HRe 4%bv Q4. rq AO2 HRe 8%bv Q8. rq AO2 HRe 9%bv Q9. rq AO2 HRe 15%bv Q15. rq AO2 HRe 16%bv Q16.
      rq AO2 HRe 19%bv Q19. rq AO2 HRe 20%bv Q20. rq AO2 HRe 22%bv Q22. rq AO2 HRe 23%bv Q23. rq AO2 HRe 27%bv Q27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q15, Q16, Q19, Q20, Q22, Q23, Q27 in VIS1.
      eapply (stage_node H HHB gp tp s0 s3 s4 s6 s7 s9 s11 S1 s LB0 LF obj key keyp v784 ents bl bc lo B shi m mo CH
                BCL OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH K0 KCE
                s msF1 mo1 M1 F fc); [exact VIS1 | exact FRZ | exact KR1 | exact (NP1 mo1 MP1) | intros X; exfalso; exact (X Hbc0)].
    - destruct (@dsp_nz (PropExec.mkFP F fc) (seg_rom asegs) M1 S1 key bc R264a SPL SPH R' (u_bseq U) Hbcn KR32
                  ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity))
          as (R2 & pw & Hms2 & AO2 & G26 & G12 & PWR & PW2 & PW1).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.

      pose proof SH1 as SH1'. destruct SH1' as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
      assert (SE : @LbA_NtS.SENV _ LY_A MI_A (lbl LB) M1 S1 obj bl bc key ents).
      { split; [exact U1|]. split; [exact KR32|].
        split; [intros i Hi; eapply sh0_of_addressable; [exact ADH1 | change (8 * (40 / 8)) with 40; clear - Hi; lia]|].
        split; [intros Hb i Hi; eapply sh0_of_addressable; [exact (SHb Hb) |]; replace (8 * bc / 8) with bc by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity); clear - Hi; lia|].
        split; [intros q k v Hq i Hi; eapply sh0_of_addressable; [exact (SHn q k v Hq) | change (8 * (32 / 8)) with 32; clear - Hi; lia]|].
        split; [exact R976a|]. split; [exact R448a|]. split; [exact SPL | exact SPH]. }
      rq AO2 HRe 2%bv A2. rq AO2 HRe 9%bv A9. rq AO2 HRe 16%bv A16. rq AO2 HRe 15%bv A15. rq AO2 HRe 23%bv A23.
      destruct (@LbA_NtS.emp_from_bb (PropExec.mkFP F fc) _ LY_A MI_A (seg_rom asegs) (lbl LB) M1 S1 obj bl bc key ents R2 pw SE Hbcn
                  A2 A9 A16 A15 A23 G26 G12 PWR PW2 PW1) as [R3 [(r & EF & Hms3 & AO3 & G25) | (Hms3 & AO3)]].
      +
        destruct EF as [v Hin]. destruct (in_split _ _ Hin) as (l1 & l2 & He).
        pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 8%bv B8. rq2 AO3 AO2 HRe 9%bv B9.
        rq2 AO3 AO2 HRe 19%bv B19. rq2 AO3 AO2 HRe 20%bv B20. rq2 AO3 AO2 HRe 22%bv B22. rq2 AO3 AO2 HRe 27%bv B27.
        rewrite B2, B3, B4, B8, B9, B19, B20, B22, B27, G25 in VIS1.
        eapply (stage_found H HH gp tp s0 s3 s4 s6 s7 s9 s11 S1 s LB0 LF obj key v784 ents bl bc lo B shi m mo
                  s msF1 mo1 M1 F fc) with (p := r) (v0 := v) (l1 := l1) (l2 := l2) (LB' := LB) (LBm' := LBm);
          [ exact VIS1 | exact FRZ | exact KR1 | exact MP1 | exact WS1 | exact R784a | exact R976a | exact SPL | exact SPH | exact V64
          | exact MI1 | exact ST1 | exact ERR1 | exact RA1 | exact TPV | exact He
          | exact U1 | exact SH1 | exact ADH1 | exact WRH1
          | exact RH1 | exact PE | exact PM | exact OWN1 | exact XP1 | exact RF1 | exact AC1 | exact S01 | exact ACL | exact LOS | apply Z.le_ge; apply Z.le_refl ].
      +
        pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 8%bv B8. rq2 AO3 AO2 HRe 9%bv B9.
        rq2 AO3 AO2 HRe 15%bv B15. rq2 AO3 AO2 HRe 16%bv B16.
        rq2 AO3 AO2 HRe 19%bv B19. rq2 AO3 AO2 HRe 20%bv B20. rq2 AO3 AO2 HRe 22%bv B22. rq2 AO3 AO2 HRe 23%bv B23. rq2 AO3 AO2 HRe 27%bv B27.
        pose proof (AO3 (26%bv : reg) ltac:(inb)) as B26. rewrite G26 in B26.
        rewrite B2, B3, B4, B8, B9, B15, B16, B19, B20, B22, B23, B27, B26 in VIS1.
        eapply (stage_node H HHB gp tp s0 s3 s4 s6 s7 s9 s11 S1 s LB0 LF obj key keyp v784 ents bl bc lo B shi m mo CH
                  BCL OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH K0 KCE
                  s msF1 mo1 M1 F fc); [exact VIS1 | exact FRZ | exact KR1 | exact (NP1 mo1 MP1) | intros _; reflexivity].
  Qed.
End NtE.
