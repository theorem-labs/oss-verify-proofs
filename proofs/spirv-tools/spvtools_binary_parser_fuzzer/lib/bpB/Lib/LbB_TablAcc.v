(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_TablStmt LbB_TablImg LbB_TablLO.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ACC_SR : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34)].
Definition ACC_KN (lo hi : Z) : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KWr (SA (EVar 33) (-16)) (ELit 16);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47);
    KRange (EVar 32) lo hi ].
Definition ACC_SCR : scripts := SCR [] [EVar 35; EVar 36] [].
Definition ACC_SCR1 : scripts := SCR [false] [EVar 35; EVar 36] [].

Lemma cell4_of_fld : forall m a v, fld ASEGS m a 4 v -> 0 <= v < 2 ^ 32 -> cellw ASEGS m a 4 v.
Proof. intros m a v F Hv. split; [cbn; lia | exact F]. Qed.

Section Acc.
  Context {HCEIL : HeapCeil}.

  Lemma acc_run : forall (entry retpc : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (slo d f1 f2 : Z)
                   (P : word -> word -> Prop),
    stk asegs m slo (bv_unsigned sp) -> aceil <= slo -> slo <= bv_unsigned sp - TL_STACK ->
    bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m -> ACONST m ->
    (forall E, E = Eseed (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       [Z_to_bv 64 d; sp; ra; Z_to_bv 64 f1; Z_to_bv 64 f2] ->
       exists R' lg, CatSim.msteps asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                              F (Z_to_bv 64 entry) fc None m (seg_rom asegs))
                                          (MS R' F (Z_to_bv 64 retpc) fc None (mem_denot E m lg) (seg_rom asegs))
         /\ log_flat E lg
         /\ forallb (fun se => expr_eqb (a_base (e_addr se)) (EVar 33) && sb_inside [(-16, 0)] (a_off (e_addr se)) (Z.of_nat (e_width se))) lg = true
         /\ kept_in KCS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R'
         /\ getr R' 1 = ra /\ getr R' 2 = sp /\ P (getr R' 10) (getr R' 11)) ->
    exists R' M1, CatSim.msteps asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (Z_to_bv 64 entry) fc None m (seg_rom asegs))
                     (MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10) (getr R' 11) (getr R' 12)
                          (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31)) F (Z_to_bv 64 retpc) fc None M1 (seg_rom asegs))
      /\ munch ((bv_unsigned sp - TL_STACK, bv_unsigned sp) :: []) m M1 /\ wmono asegs m M1 /\ mem_inv asegs M1
      /\ stk asegs M1 slo (bv_unsigned sp) /\ ACONST M1 /\ P (getr R' 10) (getr R' 11).
  Proof.
    intros entry retpc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m slo d f1 f2 P ST CE LO S47 MI AC RUN.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    set (spz := bv_unsigned sp) in *.
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    unfold TL_STACK in *.
    destruct (RUN _ eq_refl) as (R' & lg & MS & Hlf & SB & KK & G1 & G2 & HP).
    set (E := Eseed (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    [Z_to_bv 64 d; sp; ra; Z_to_bv 64 f1; Z_to_bv 64 f2]) in *.
    set (M1 := mem_denot E m lg) in *.
    assert (HB : bv_unsigned (edenot E (EVar 33)) = spz) by (subst E; evs; reflexivity).
    assert (MU : munch [(spz - 16, spz)] m M1).
    { pose proof (munch_mem_denot_sb [(-16, 0)] (EVar 33) E m _ Hlf SB) as MU.
      rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
    assert (WM : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ MS MI).
    assert (ST1 : stk asegs M1 slo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (AC1 : ACONST M1).
    { eapply (ACONST_frame _ _ _ AC MU WM). apply Forall_cons; [|apply Forall_nil].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (RF : rfull R') by (exact (msteps_full asegs _ _ MS (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))).
    assert (E3 : R' = mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10) (getr R' 11) (getr R' 12)
                          (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31)).
    { rewrite (rfull_eq R' RF) at 1.
      rewrite G1, G2, (KK 3%bv ltac:(inb)), (KK 4%bv ltac:(inb)), (KK 8%bv ltac:(inb)), (KK 9%bv ltac:(inb)),
              (KK 18%bv ltac:(inb)), (KK 19%bv ltac:(inb)), (KK 20%bv ltac:(inb)), (KK 21%bv ltac:(inb)), (KK 22%bv ltac:(inb)),
              (KK 23%bv ltac:(inb)), (KK 24%bv ltac:(inb)), (KK 25%bv ltac:(inb)), (KK 26%bv ltac:(inb)), (KK 27%bv ltac:(inb)).
      reflexivity. }
    clearbody M1. clear HB SB Hlf. clearbody E.
    exists R', M1. rewrite <- E3. split; [exact MS|].
    split; [eapply munch_weaken; [|exact MU]; intros z Hz; cbn [outside] in Hz |- *; lia|].
    split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1 | exact HP].
  Qed.
  Theorem odesc_operands_okA : odesc_operands_stmtA.
  Proof.
    intros [[d t] v] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hd & Ha0).
    destruct (odescA_facts d t v Hd) as (r & Hfi & Htg & Hv & D0 & D1 & D4 & D52 & FL & Q0 & Q1 & Q2 & Q3 & SP & LEN).
    destruct (FL m (conj MI AC)) as (F0 & F4 & F8 & GZ).
    assert (HSP : Zlen SPANS = 1151) by reflexivity. rewrite HSP in Q3.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    destruct (acc_run AT_ODESC_OPERANDS 0xfde04 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo d (v_first r) (v_count r)
                (fun r0 r1 => r0 = Z_to_bv 64 (0x25260 + 4 * v_first r) /\ r1 = Z_to_bv 64 (v_count r)) ST CE LO S47 MI AC)
      as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & (P10 & P11)).
    { intros E HE.
      assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
      { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
      pose proof (ACONST_shbase m AC) as [CG CS].
      assert (HK : know_ok asegs E m (kn_fix 4 [0xfde04] ACC_SCR1 AT_ODESC_OPERANDS ACC_SR (ACC_KN 0x48260 (0x48260 + 64740)) 37)).
      { kn_eval. unfold know_ok. subst E.
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 4); lia]|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 8); lia]|].
        apply Forall_nil. }
      assert (C4 : cellw ASEGS m (d + 4) 4 (v_first r)) by (apply cell4_of_fld; [exact F4 | lia]).
      assert (C8 : cellw ASEGS m (d + 8) 4 (v_count r)) by (apply cell4_of_fld; [exact F8 | lia]).
      change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AT_ODESC_OPERANDS) fc None m (seg_rom asegs))
        with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 (Z_to_bv 64 AT_ODESC_OPERANDS) m (seg_rom asegs)).
      xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        AT_ODESC_OPERANDS m (seg_rom asegs) HR HK 40%nat [0xfde04] ACC_SCR1 37%N.
      { split_scs.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C8); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity].
        - cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_mul; rewrite br_ltu by lia; bool_lia.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C4); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms end end.
      eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
      subst E.
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      split; [exact G1|]. split; [exact G2|]. split.
      + rewrite G10, TablLib.zbv_mul, TablLib.zbv_add. f_equal. lia.
      + exact G11. }
    eapply evt_of_msteps; [exact MS|].
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    exists (0x25260 + 4 * v_first r), (v_span r). split; [exact Htg|]. split; [exact SP|]. split; [exact P10|].
    rewrite LEN. exact P11.
  Qed.
  Theorem edesc_operands_okA : edesc_operands_stmtA.
  Proof.
    intros [[d t] v] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hd & Ha0).
    destruct (edescA_facts d t v Hd) as (r & Hfi & Htg & Hv & D0 & D1 & D4 & D28 & FL & Q0 & Q1 & Q2 & Q3 & SP & LEN).
    destruct (FL m (conj MI AC)) as (F0 & F4 & F8 & GZ).
    assert (HSP : Zlen SPANS = 1151) by reflexivity. rewrite HSP in Q3.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    destruct (acc_run AT_EDESC_OPERANDS 0xfdfb0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo d (v_first r) (v_count r)
                (fun r0 r1 => r0 = Z_to_bv 64 (0x25260 + 4 * v_first r) /\ r1 = Z_to_bv 64 (v_count r)) ST CE LO S47 MI AC)
      as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & (P10 & P11)).
    { intros E HE.
      assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
      { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
      pose proof (ACONST_shbase m AC) as [CG CS].
      assert (HK : know_ok asegs E m (kn_fix 4 [0xfdfb0] ACC_SCR1 AT_EDESC_OPERANDS ACC_SR (ACC_KN 0x5be80 (0x5be80 + 14000)) 37)).
      { kn_eval. unfold know_ok. subst E.
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 4); lia]|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 8); lia]|].
        apply Forall_nil. }
      assert (C4 : cellw ASEGS m (d + 4) 4 (v_first r)) by (apply cell4_of_fld; [exact F4 | lia]).
      assert (C8 : cellw ASEGS m (d + 8) 4 (v_count r)) by (apply cell4_of_fld; [exact F8 | lia]).
      change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AT_EDESC_OPERANDS) fc None m (seg_rom asegs))
        with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 (Z_to_bv 64 AT_EDESC_OPERANDS) m (seg_rom asegs)).
      xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        AT_EDESC_OPERANDS m (seg_rom asegs) HR HK 40%nat [0xfdfb0] ACC_SCR1 37%N.
      { split_scs.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C8); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity].
        - cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_mul; rewrite br_ltu by lia; bool_lia.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C4); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms end end.
      eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
      subst E.
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      split; [exact G1|]. split; [exact G2|]. split.
      + rewrite G10, TablLib.zbv_mul, TablLib.zbv_add. f_equal. lia.
      + exact G11. }
    eapply evt_of_msteps; [exact MS|].
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    exists (0x25260 + 4 * v_first r), (v_span r). split; [exact Htg|]. split; [exact SP|]. split; [exact P10|].
    rewrite LEN. exact P11.
  Qed.
  Theorem idesc_operands_okA : idesc_operands_stmtA.
  Proof.
    intros [d op] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hd & Ha0).
    destruct (idescA_facts d op Hd) as (r & Hfi & Hop & Htg & D0 & D1 & D4 & D60 & FL & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & SP & LEN & HCS).
    destruct (FL m (conj MI AC)) as (F0 & F4 & F8 & F16 & F20 & GZ).
    assert (HSP : Zlen SPANS = 1151) by reflexivity. rewrite HSP in Q3.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    destruct (acc_run AT_IDESC_OPERANDS 0xfde94 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo d (i_first r) (i_count r)
                (fun r0 r1 => r0 = Z_to_bv 64 (0x25260 + 4 * i_first r) /\ r1 = Z_to_bv 64 (i_count r)) ST CE LO S47 MI AC)
      as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & (P10 & P11)).
    { intros E HE.
      assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
      { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
      pose proof (ACONST_shbase m AC) as [CG CS].
      assert (HK : know_ok asegs E m (kn_fix 4 [0xfde94] ACC_SCR1 AT_IDESC_OPERANDS ACC_SR (ACC_KN 0x381c0 (0x381c0 + 52560)) 37)).
      { kn_eval. unfold know_ok. subst E.
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 8); lia]|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 12); lia]|].
        apply Forall_nil. }
      assert (C4 : cellw ASEGS m (d + 8) 4 (i_first r)) by (apply cell4_of_fld; [exact F4 | lia]).
      assert (C8 : cellw ASEGS m (d + 12) 4 (i_count r)) by (apply cell4_of_fld; [exact F8 | lia]).
      change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AT_IDESC_OPERANDS) fc None m (seg_rom asegs))
        with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 (Z_to_bv 64 AT_IDESC_OPERANDS) m (seg_rom asegs)).
      xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        AT_IDESC_OPERANDS m (seg_rom asegs) HR HK 40%nat [0xfde94] ACC_SCR1 37%N.
      { split_scs.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C8); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity].
        - cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_mul; rewrite br_ltu by lia; bool_lia.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C4); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms end end.
      eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
      subst E.
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      split; [exact G1|]. split; [exact G2|]. split.
      + rewrite G10, TablLib.zbv_mul, TablLib.zbv_add. f_equal. lia.
      + exact G11. }
    eapply evt_of_msteps; [exact MS|].
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    exists (0x25260 + 4 * i_first r), (i_span r). split; [exact Htg|]. split; [exact SP|]. split; [exact P10|].
    rewrite LEN. exact P11.
  Qed.
  Theorem idesc_name_okA : idesc_name_stmtA.
  Proof.
    intros [d op] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hd & Ha0).
    destruct (idescA_facts d op Hd) as (r & Hfi & Hop & Htg & D0 & D1 & D4 & D60 & FL & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & SP & LEN & HCS).
    destruct (FL m (conj MI AC)) as (F0 & F4 & F8 & F16 & F20 & GZ).
    assert (HSP : Zlen SPANS = 1151) by reflexivity. rewrite HSP in Q3.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    destruct (acc_run AT_IDESC_NAME 0xfdf20 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo d (i_nfirst r) (i_ncount r)
                (fun r0 r1 => r0 = Z_to_bv 64 (0x268c0 + i_nfirst r) /\ r1 = Z_to_bv 64 (i_ncount r)) ST CE LO S47 MI AC)
      as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & (P10 & P11)).
    { intros E HE.
      assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
      { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
        repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
      pose proof (ACONST_shbase m AC) as [CG CS].
      assert (HK : know_ok asegs E m (kn_fix 4 [0xfdf20] ACC_SCR1 AT_IDESC_NAME ACC_SR (ACC_KN 0x381c0 (0x381c0 + 52560)) 37)).
      { kn_eval. unfold know_ok. subst E.
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
        apply Forall_cons.
        { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                             | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
        apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
        apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 16); lia]|].
        apply Forall_cons; [eapply kshadow0; [evs; rewrite TablLib.zbv_add; reflexivity | clear - D0 D1; lia | apply (GZ 20); lia]|].
        apply Forall_nil. }
      assert (C4 : cellw ASEGS m (d + 16) 4 (i_nfirst r)) by (apply cell4_of_fld; [exact F16 | lia]).
      assert (C8 : cellw ASEGS m (d + 20) 4 (i_ncount r)) by (apply cell4_of_fld; [exact F20 | lia]).
      change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AT_IDESC_NAME) fc None m (seg_rom asegs))
        with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 (Z_to_bv 64 AT_IDESC_NAME) m (seg_rom asegs)).
      xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        AT_IDESC_NAME m (seg_rom asegs) HR HK 40%nat [0xfdf20] ACC_SCR1 37%N.
      { split_scs.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C8); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity].
        - cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_mul; rewrite br_ltu by lia; bool_lia.
        - eapply (sc_read_cellw asegs _ _ _ _ 4%N _ _ C4); [lia | subst E; unfold adenot; cbn [a_base a_off]; evs; rewrite v_addi_Z by lia; reflexivity
                                                          | subst E; evs; reflexivity]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms end end.
      eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
      subst E.
      split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      split; [exact G1|]. split; [exact G2|]. split.
      + rewrite G10, ?TablLib.zbv_mul, ?TablLib.zbv_add. f_equal. lia.
      + exact G11. }
    eapply evt_of_msteps; [exact MS|].
    step.
    apply evt_done.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
    exists (0x268c0 + i_nfirst r), (i_ncount r - 1). split; [exact HCS | exact P10].
  Qed.
End Acc.
