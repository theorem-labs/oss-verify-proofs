(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_VecD1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section VecD2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HANN : annotate_gen_stmt.

  Definition vd_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Dd V P n lo shi : Z) (m2 : mem) : machine_state -> Prop :=
    fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (4 * n)) a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 AOPDEL2) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp - 32); (sh P, sh P + nsh (4 * n));
                (bv_unsigned sp - 48 - 4096, bv_unsigned sp - 48)] m2 m'
      /\ wmono asegs m2 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ SHAD m' P (shadow_of (4 * n)) /\ ACONST m' /\ stack0 m' lo shi
      /\ rw_cells asegs m' V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))].

#[local] Definition HTLbAVecD2_0 : list (reg * expr) := [(2%bv, EAlu ALU_ADD (EVar 33) (ELit (-48))); (8%bv, EVar 32); (9%bv, ELit 2147450880); (18%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 32) (ELit 3)) (ELit 2147450880))].
Definition vdc_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 33) (-48)) 8 (EVar 32); KWord (SA (EVar 33) (-40)) 8 (ELit 0xe8ef4);
    KWord (SA (EVar 32) 0) 8 (EVar 34); KWord (SA (EVar 34) 0) 8 (EVar 35);
    KWord (SA (EVar 34) 8) 8 (EVar 35); KWord (SA (EVar 34) 16) 8 (EVar 37);
    KWr (SA (EVar 33) (-64)) (ELit 64);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KAlign (EVar 33) 16;
    KRange (EVar 32) (2 ^ 45) (2 ^ 47); KAlign (EVar 32) 8;
    KRange (EVar 34) AIMG_TOP (2 ^ 47); KAlign (EVar 34) 8;
    KRange (EVar 35) AIMG_TOP (2 ^ 47); KAlign (EVar 35) 16;
    KRange (EVar 36) 1 (2 ^ 24); KRange (EVar 37) AIMG_TOP (2 ^ 47) ].
Definition vdc_knF : list kentry :=
  Eval vm_compute in kn_fix 30 [AANNOTATE_CC] (SCR (repeat false 30) [] []) VD_SHR_RET (srs sr_id HTLbAVecD2_0) vdc_kn 40.
Definition vdc_x := sym_exec asegs 400 true [AANNOTATE_CC] (SCR (repeat false 30) [] []) (SS VD_SHR_RET (srs sr_id HTLbAVecD2_0) [] vdc_knF 40) [].
Definition vdc_ss : sym_state := Eval vm_compute in fst (fst vdc_x).
Definition vdc_scs : list sidecond := Eval vm_compute in snd (fst vdc_x).
Definition vdc_scr : scripts := Eval vm_compute in snd vdc_x.
Lemma vdc_eq : vdc_x = (vdc_ss, vdc_scs, vdc_scr).
Proof. vm_compute. reflexivity. Qed.

Definition vdd_kn : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL); KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit SHBASE);
    KWord (SA (EVar 33) (-48)) 8 (EVar 32); KWord (SA (EVar 33) (-40)) 8 (ELit 0xe8f10);
    KWord (SA (EVar 33) (-32)) 8 (EVar 38); KWord (SA (EVar 33) (-24)) 8 (EVar 39);
    KWord (SA (EVar 33) (-16)) 8 (EVar 40); KWord (SA (EVar 33) (-8)) 8 (EVar 41);
    KWord (SA (EVar 32) 0) 8 (EVar 34); KWord (SA (EVar 34) 0) 8 (EVar 35);
    KWord (SA (EVar 34) 16) 8 (EVar 37);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47); KAlign (EVar 33) 16;
    KRange (EVar 32) (2 ^ 45) (2 ^ 47); KAlign (EVar 32) 8;
    KRange (EVar 34) AIMG_TOP (2 ^ 47); KAlign (EVar 34) 8;
    KRange (EVar 35) AIMG_TOP (2 ^ 47); KAlign (EVar 35) 16;
    KRange (EVar 36) 1 (2 ^ 24); KRange (EVar 37) AIMG_TOP (2 ^ 47) ].
Definition vdd_knF : list kentry :=
  Eval vm_compute in kn_fix 30 [AOPDEL2] (SCR (repeat false 30) [] []) VD_DEL_RET (srs sr_id HTLbAVecD2_0) vdd_kn 50.
Definition vdd_x := sym_exec asegs 400 true [AOPDEL2] (SCR (repeat false 30) [] []) (SS VD_DEL_RET (srs sr_id HTLbAVecD2_0) [] vdd_knF 50) [].
Definition vdd_ss : sym_state := Eval vm_compute in fst (fst vdd_x).
Definition vdd_scs : list sidecond := Eval vm_compute in snd (fst vdd_x).
Definition vdd_scr : scripts := Eval vm_compute in snd vdd_x.
Lemma vdd_eq : vdd_x = (vdd_ss, vdd_scs, vdd_scr).
Proof. vm_compute. reflexivity. Qed.

  Lemma vd_b : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m2 : mem) (Dd V P n lo shi : Z),
    stk asegs m2 lo (bv_unsigned sp) -> mem_inv asegs m2 ->
    rw_cells asegs m2 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))] -> rw_cells asegs m2 Dd [C8 (wz V)] ->
    rw_cells asegs m2 (bv_unsigned sp - 48) [C8 (wz Dd); C8 (wz 0xe8ef4); C8 s2; C8 s1; C8 s0; C8 ra] ->
    SHAD m2 V (repeat (b8 0) 3) -> stack0 m2 lo shi -> SHAD m2 P (cc_gen (4 * n) 0) -> ACONST m2 ->
    Dd mod 8 = 0 -> bv_unsigned sp <= Dd -> Dd + 8 <= shi -> V mod 8 = 0 -> aapp V 24 ->
    (V + 24 <= bv_unsigned sp - VD_STACK \/ bv_unsigned sp <= V) ->
    1 <= n <= 2 ^ 24 -> aapp P (4 * n) -> P mod 16 = 0 -> (P + 4 * n <= V \/ V + 24 <= P) ->
    aceil <= lo -> lo <= bv_unsigned sp - VD_STACK -> bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 ->
    evt asegs (vd_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dd V P n lo shi m2)
      (MS (mkR (Z_to_bv 64 VD_SHR_RET) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp w0 w1 w2 (Z_to_bv 64 Dd) (Z_to_bv 64 0x7fff8000)
               d0 d1 d2 d3 d4 d5 d6 d7 (shw Dd) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
          F (Z_to_bv 64 VD_SHR_RET) fc None m2 (seg_rom asegs)).
Proof.
    intros until shi. intros ST MI CV CD CF SV S0 SP AC D8 DSP DHI V8 VA VAP NB PA P16 PV CE LO SP16 SPR.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold VD_STACK, AINTRIN_STACK in LO, VAP.
    pose proof (stack0_bounds m2 lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (aapp_bounds V 24 VA ltac:(lia)) as (VB1 & VB2 & VB3 & VB4 & VB5).
    pose proof (aapp_bounds P (4 * n) PA ltac:(lia)) as (PB1 & PB2 & PB3 & PB4 & PB5).
    unfold AIMG_TOP in VB1, PB1. unfold AAPP_HI in VB3, PB3.
    assert (SHE : forall x, sh x = 2147450880 + x / 8) by (intros x; reflexivity).
    assert (SHT : sh AIMG_TOP < 2 ^ 32) by reflexivity.
    match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) => remember r as R eqn:HR0 end.
    pose (E := Eseed R [Z_to_bv 64 Dd; Z_to_bv 64 spz; Z_to_bv 64 V; Z_to_bv 64 P; Z_to_bv 64 n; Z_to_bv 64 (P + 4 * n)]).
    assert (HR : regs_ok E (srs sr_id HTLbAVecD2_0) R).
    { unfold HTLbAVecD2_0. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        first [reflexivity | rewrite w_addm by lia; reflexivity]. }
    pose proof (ACONST_shbase m2 AC) as [CG CS].
    assert (GZV : gz m2 V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; lia]).
    assert (SDD : sh0 m2 Dd) by (eapply sh0_of_stack0; [exact S0 | lia]).
    assert (HK : know_ok asegs E m2 vdc_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m2 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m2 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CF 0%nat (C8 (wz Dd)). }
      apply Forall_cons. { kword_cell CF 8%nat (C8 (wz 0xe8ef4)). }
      apply Forall_cons. { kword_cell CD 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CV 0%nat (C8 (wz P)). }
      apply Forall_cons. { kword_cell CV 8%nat (C8 (wz P)). }
      apply Forall_cons. { kword_cell CV 16%nat (C8 (wz (P + 4 * n))). }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 10 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    assert (HSC1 : scs_denot asegs m2 E vdc_scs).
    { unfold vdc_scs. split_scs.
      all: clear - E VA SPR LO CE ACF1 ACF2 PB1 PB2 PB3 VB1 VB2 VB3 SB0 DSP DHI NB.
      all: unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in VA.
      all: vd_sc. }
    destruct (@run_sound (PropExec.mkFP F fc) asegs 400 [AANNOTATE_CC] (SCR (repeat false 30) [] []) VD_SHR_RET (srs sr_id HTLbAVecD2_0) vdc_knF 40
                vdc_ss vdc_scs vdc_scr E m2 (seg_rom asegs) R vdc_eq HR HK HSC1) as (R' & HR' & Hlf & Hms).
    clear HK HSC1.
    unfold vdc_ss in HR', Hlf, Hms. cbn [s_pc s_regs s_log] in HR', Hlf, Hms.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m2 lg) in Hms; set (M1 := mem_denot E m2 lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 18%bv L18.
    rewrite w_addm in L2 by lia.

    assert (WS1 : forall a, spz - 64 <= a -> a + 8 <= spz -> wr_at asegs m2 a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m2 lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (MU1 : munch [(spz - 48, spz - 32); (spz - 48 - 4096, spz - 48)] m2 M1).
    { subst M1. clear - Hlf VAP SPR LO CE ACF1 ACF2 VB1 VB2 VB3. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m2 M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (SVP : sh P + nsh (4 * n) <= V \/ V + 24 <= sh P)
      by (apply (aapp_disjoint_sh V 24 P (4 * n) VA); unfold AAPP_HI; lia).
    assert (SPH : sh P + nsh (4 * n) <= AHI_LO)
      by (apply sh_nsh_high; [lia | lia | unfold AAPP_HI; lia]).
    assert (SPA : sh P + nsh (4 * n) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHV : sh V + 3 <= sh P \/ sh P + nsh (4 * n) <= sh V).
    { clear - PV V8 P16 NB. unfold sh, nsh. Z.div_mod_to_equations. nia. }
    assert (SB1 : SHAD M1 P (cc_gen (4 * n) 0)).
    { eapply SHAD_transport; [exact SP | exact MU1 | exact WM1 |]. rewrite cc_gen_length by lia. cbn.
      rewrite !SHE in *. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in PA. unfold AHI_LO in SPH. Z.div_mod_to_equations. lia. }
    assert (SV1 : SHAD M1 V (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV | exact MU1 | exact WM1 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      rewrite !SHE. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA. Z.div_mod_to_equations. lia. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (AC1 : ACONST M1).
    { eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 |].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia]|].
      apply Forall_cons; [apply aconst_ok_high; [cbn; lia | right; left; cbn; lia] | apply Forall_nil]. }
    assert (CV1 : rw_cells asegs M1 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))])
      by (eapply rw_cells_transport; [exact CV | exact MU1 | exact WM1 | cbn; lia]).
    assert (CD1 : rw_cells asegs M1 Dd [C8 (wz V)])
      by (eapply rw_cells_transport; [exact CD | exact MU1 | exact WM1 | cbn; lia]).
    assert (CF1 : rw_cells asegs M1 (spz - 48) [C8 (wz Dd); C8 (wz 0xe8f10); C8 s2; C8 s1; C8 s0; C8 ra]).
    { change [C8 (wz Dd); C8 (wz 0xe8ef4); C8 s2; C8 s1; C8 s0; C8 ra]
        with ([C8 (wz Dd); C8 (wz 0xe8ef4)] ++ [C8 s2; C8 s1; C8 s0; C8 ra]) in CF.
      apply rw_cells_app in CF as [_ CFh].
      replace (spz - 48 + Z.of_nat (cells_size [C8 (wz Dd); C8 (wz 0xe8ef4)])) with (spz - 32) in CFh by (cbn; lia).
      apply rw_cells_cons8_c.
      { subst M1. lgcell Hlf (WS1 (spz - 48) ltac:(lia) ltac:(lia)) 1%nat. }
      apply rw_cells_cons8_c.
      { subst M1. lgcell Hlf (WS1 (spz - 48 + 8) ltac:(lia) ltac:(lia)) 2%nat. }
      replace (spz - 48 + 8 + 8) with (spz - 32) by lia.
      eapply rw_cells_transport; [exact CFh | exact MU1 | exact WM1 | cbn; lia]. }

    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L11, L12, L13, L18.
    clear HRe HR' Hlf Hms HF1 L1 L2 L8 L9 L10 L11 L12 L13 L18.
    eapply evt_cut.
    { eapply HANN with (beg := P) (len := 4 * n) (oldmid := 0) (newmid := 4 * n) (lo := lo); rewrite ?u64_of_Z by lia.
      - reflexivity.
      - reflexivity.
      - rewrite Z.add_0_r. reflexivity.
      - reflexivity.
      - Z.div_mod_to_equations; lia.
      - lia.
      - lia.
      - lia.
      - exact PA.
      - unfold AAPP_HI; lia.
      - exact SB1.
      - exact (proj1 (stk_split asegs M1 lo (spz - 48) spz ST1 ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact MI1.
      - exact AC1.
      - eapply aapp_in_app_mem; [exact PA | lia | lia]. }
    intros ms2 POST2.
    destruct POST2 as (w0' & w1' & w2' & d0' & d1' & d2' & d3' & d4' & d5' & d6' & d7' & w3' & w4' & w5' & w6' & m3 & EQ2 & MU2 & WM2 & MI2 & ST2 & SH2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia. unfold AINTRIN_STACK in MU2.
    rewrite (ret_pc_even 0xe90c8 ltac:(lia) eq_refl).

    assert (CV2 : rw_cells asegs m3 V [C8 (wz P); C8 (wz P); C8 (wz (P + 4 * n))])
      by (eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; lia]).
    assert (CD2 : rw_cells asegs m3 Dd [C8 (wz V)])
      by (eapply rw_cells_transport; [exact CD1 | exact MU2 | exact WM2 | cbn; unfold AHI_LO in SPH; lia]).
    assert (CF2 : rw_cells asegs m3 (spz - 48) [C8 (wz Dd); C8 (wz 0xe8f10); C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CF1 | exact MU2 | exact WM2 | cbn; unfold AHI_LO in SPH; lia]).
    assert (SV2 : SHAD m3 V (repeat (b8 0) 3)).
    { eapply SHAD_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [length repeat Z.of_nat Pos.of_succ_nat]. cbn.
      assert (sh V + 3 <= 2 ^ 45 - 8192)
        by (rewrite !SHE; unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in VA; Z.div_mod_to_equations; lia).
      lia. }
    assert (S02 : stack0 m3 lo shi).
    { eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; cbn; exact SPA|].
      apply Forall_cons; [apply stack0_ok_app; cbn; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ST2f : stk asegs m3 lo spz).
    { apply (stk_merge asegs m3 lo (spz - 48) spz); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 lo (spz - 48) spz ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      cbn. unfold AHI_LO in SPH. lia. }
    assert (MU12 : munch [(spz - 48, spz - 32); (sh P, sh P + nsh (4 * n)); (spz - 48 - 4096, spz - 48)] m2 m3).
    { eapply munch_trans; [eapply munch_weaken; [|exact MU1] | eapply munch_weaken; [|exact MU2]];
        intros x Hx; cbn [outside] in *; lia. }
    assert (WM12 : wmono asegs m2 m3) by exact (wmono_trans asegs _ _ _ WM1 WM2).
    clear CV CD CF SV SP AC MI ST S0 CV1 CD1 CF1 SV1 SB1 S01 AC1 MI1 ST1 MU1 MU2 WM1 WM2 ST2 GZV SDD CG CS.

    match goal with |- evt _ _ (MS ?r _ _ _ _ _ _) => remember r as R2 eqn:HR20 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 Dd; Z_to_bv 64 spz; Z_to_bv 64 V; Z_to_bv 64 P; Z_to_bv 64 n; Z_to_bv 64 (P + 4 * n);
                          s2; s1; s0; ra]).
    assert (HR2 : regs_ok E2 (srs sr_id HTLbAVecD2_0) R2).
    { unfold HTLbAVecD2_0. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs;
        first [reflexivity | rewrite w_addm by lia; reflexivity]. }
    pose proof (ACONST_shbase m3 AC2) as [CG3 CS3].
    assert (GZV3 : gz m3 V 24) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV2 | cbn; lia]).
    assert (SDD3 : sh0 m3 Dd) by (eapply sh0_of_stack0; [exact S02 | lia]).
    assert (HK2 : know_ok asegs E2 m3 vdd_knF).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E2 m3 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG3 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E2 m3 0x191038 _ 0%nat (C8 (wz SHBASE))); [exact CS3 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { kword_cell CF2 0%nat (C8 (wz Dd)). }
      apply Forall_cons. { kword_cell CF2 8%nat (C8 (wz 0xe8f10)). }
      apply Forall_cons. { kword_cell CF2 16%nat (C8 s2). }
      apply Forall_cons. { kword_cell CF2 24%nat (C8 s1). }
      apply Forall_cons. { kword_cell CF2 32%nat (C8 s0). }
      apply Forall_cons. { kword_cell CF2 40%nat (C8 ra). }
      apply Forall_cons. { kword_cell CD2 0%nat (C8 (wz V)). }
      apply Forall_cons. { kword_cell CV2 0%nat (C8 (wz P)). }
      apply Forall_cons. { kword_cell CV2 16%nat (C8 (wz (P + 4 * n))). }
      do 10 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; unfold AIMG_TOP; lia|]).
      know_tac. }
    assert (HSC2 : scs_denot asegs m3 E2 vdd_scs) by (unfold vdd_scs; split_scs).
    destruct (@run_sound (PropExec.mkFP F fc) asegs 400 [AOPDEL2] (SCR (repeat false 30) [] []) VD_DEL_RET (srs sr_id HTLbAVecD2_0) vdd_knF 50
                vdd_ss vdd_scs vdd_scr E2 m3 (seg_rom asegs) R2 vdd_eq HR2 HK2 HSC2) as (R3 & HR3 & Hlf3 & Hms3).
    clear HK2 HSC2.
    unfold vdd_ss in HR3, Hlf3, Hms3. cbn [s_pc s_regs s_log mem_denot] in HR3, Hlf3, Hms3.
    assert (HF2 : rfull R2) by (rewrite HR20; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms3 HF2) as HF3. cbn [ms_regs] in HF3.
    readback HR3 HF3 HR20 HRe3.
    rreg HR3 1%bv K1. rreg HR3 2%bv K2. rreg HR3 8%bv K8. rreg HR3 9%bv K9. rreg HR3 10%bv K10. rreg HR3 11%bv K11. rreg HR3 18%bv K18.
    rewrite vd_mul_u, vd_add_u in K11. replace (-1 * P + (P + 4 * n)) with (4 * n) in K11 by lia.
    eapply evt_of_msteps; [exact Hms3|].
    rewrite mkst_MS, HRe3, K1, K2, K8, K9, K10, K11, K18, <- Hsp.
    apply evt_done. do 13 eexists. exists m3.
    split; [reflexivity|].
    split; [exact MU12|]. split; [exact WM12|]. split; [exact MI2|]. split; [exact ST2f|].
    split; [rewrite <- cc_gen_full; exact SH2|]. split; [exact AC2|]. split; [exact S02 | exact CV2].
  Qed.
End VecD2.
