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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_Own LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_TablImg LbB_TablLO LbB_TablAcc.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TSW : Z := 0x17eb20.
Definition TS_RET1 : Z := 0xfeaa0.
Definition TS_RET0 : Z := 0xfeab4.
Definition tstr_ptr (i : Z) : Z := fst (nth (Z.to_nat i) TSTR_A (0, 0)).

Definition le8z (v : Z) : list Z :=
  [v mod 256; (v / 256) mod 256; (v / (256 * 256)) mod 256; (v / (256 * 256 * 256)) mod 256;
   (v / (256 * 256 * 256 * 256)) mod 256; (v / (256 * 256 * 256 * 256 * 256)) mod 256;
   (v / (256 * 256 * 256 * 256 * 256 * 256)) mod 256; (v / (256 * 256 * 256 * 256 * 256 * 256 * 256)) mod 256].

Lemma le8z_bytes : forall v, 0 <= v < 2 ^ 64 -> map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 v)) = le8z v.
Proof.
  intros v Hv. unfold word_to_le_bytes, le8z. rewrite Z_to_bv_unsigned, bv_wrap64_mod, (Z.mod_small v) by lia.
  cbn [Z_to_le_bytes map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite !Z.div_div by lia. reflexivity.
Qed.

Definition tsw_okb : bool :=
  forallb (fun i => (0 <=? tstr_ptr i) && (tstr_ptr i <? 2 ^ 47) &&
                    match rom_rd ASEGS (TSW + 8 * i) 8 with Some bs => list_eqb bs (le8z (tstr_ptr i)) | None => false end)
          (map Z.of_nat (seq 0 108)).
Lemma tsw_ok : tsw_okb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tsw_cell : forall m i, relro0 m -> 0 <= i < 108 ->
  cellw ASEGS m (TSW + 8 * i) 8 (tstr_ptr i) /\ 0 <= tstr_ptr i < 2 ^ 47.
Proof.
  intros m i HR Hi. pose proof tsw_ok as T. unfold tsw_okb in T. rewrite forallb_forall in T.
  assert (Hin : In i (map Z.of_nat (seq 0 108))).
  { apply in_map_iff. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia. }
  specialize (T i Hin). apply andb_prop in T as [T Hr]. apply andb_prop in T as [T0 T1].
  apply Z.leb_le in T0. apply Z.ltb_lt in T1. split; [|lia].
  unfold rom_rd in Hr. destruct (PropExec.rdn ASEGS (fun _ => None) (Z_to_bv 64 (TSW + 8 * i)) 8) as [bs|] eqn:E; [|discriminate].
  apply list_eqb_eq in Hr. split; [cbn; lia|]. change (N.to_nat 8) with 8%nat.
  rewrite (rdn_clear ASEGS m (TSW + 8 * i) 8); [| intros j Hj; apply HR; unfold TSW in *; lia | unfold TSW; lia | unfold TSW; cbn; lia].
  rewrite E. f_equal. apply map_unsigned_inj. rewrite Hr. symmetry. apply le8z_bytes. lia.
Qed.

Lemma tstr_ptr_in : forall i, 0 <= i < 108 -> In (tstr_ptr i, snd (nth (Z.to_nat i) TSTR_A (0, 0))) (ti_tstr_dflt tiA :: ti_tstr tiA).
Proof.
  intros i Hi. right. cbn [ti_tstr tiA]. unfold tstr_ptr. rewrite <- surjective_pairing.
  apply nth_In. change (length TSTR_A) with 108%nat. lia.
Qed.

Section TS.
  Context {HCEIL : HeapCeil}.

  Theorem operand_type_str_okA : operand_type_str_stmtA.
  Proof.
    intros x ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0 & HRL).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr.
    unfold TL_STACK in *.
    pose proof (ACONST_shbase m AC) as [CG CS].
    destruct (Z_lt_le_dec 107 x) as [Hhi | Hle].
    -
      destruct (acc_run AT_OPERAND_TYPE_STR TS_RET0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m lo x 0 0 (fun r0 _ => r0 = Z_to_bv 64 0x61940) ST CE LO S47 MI AC)
        as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & P10).
      { intros E HE.
        assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
        { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
          repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }
        assert (HK : know_ok asegs E m (ACC_KN 108 4294967295)).
        { unfold ACC_KN, know_ok. subst E.
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_nil. }
        change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AT_OPERAND_TYPE_STR) fc None m (seg_rom asegs))
          with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   (Z_to_bv 64 AT_OPERAND_TYPE_STR) m (seg_rom asegs)).
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPERAND_TYPE_STR m (seg_rom asegs) HR HK 40%nat [TS_RET0] ACC_SCR 37%N.
        { split_scs. }
        lazymatch type of Hlf with log_flat _ ?lg =>
          lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
            change mm with (mem_denot E m lg) in Hms end end.
        eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
        subst E.
        split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10.
        split; [exact G1|]. split; [exact G2|]. exact G10. }
      eapply evt_of_msteps; [exact MS|].
      step.
      apply evt_done.
      exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
        (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
      exists 0x61940, 7. split; [exact (tstrA_facts (0x61940, 7) (or_introl eq_refl))|]. split; [exact P10|].
      unfold tstrA_of. destruct (Z.ltb_spec x 108); [lia|]. rewrite Bool.andb_false_r. reflexivity.
    -
      destruct (tsw_cell m x HRL ltac:(lia)) as [CELL PB].
      assert (SH : sh0 m (TSW + 8 * x)).
      { eapply (sh0_global m 0x17eb20 864 1056); [exact AC | exact in_g_tstrsw | lia |].
        change (8 * (864 / 8)) with 864. unfold TSW. lia. }
      destruct (acc_run AT_OPERAND_TYPE_STR TS_RET1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m lo x (tstr_ptr x) 0 (fun r0 _ => r0 = Z_to_bv 64 (tstr_ptr x)) ST CE LO S47 MI AC)
        as (R' & M1 & MS & MU & WM & MI1 & ST1 & AC1 & P10).
      { intros E HE.
        assert (HR : regs_ok E ACC_SR (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)).
        { subst E. unfold ACC_SR. apply regs_ok_srs; [apply regs_ok_seed|].
          repeat apply Forall_cons; try apply Forall_nil; (split; [intros X; discriminate X|]); evs; first [exact Ha0 | reflexivity]. }

        assert (HK : know_ok asegs E m (ACC_KN 0 107 ++ [KWord (SA (EVar 32) 2147646820) 1 (ELit 0)])).
        { unfold ACC_KN, know_ok. subst E.
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply (kword_of_rw_cells asegs _ m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
          apply Forall_cons.
          { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
          apply Forall_cons; [cbn [kentry_ok]; evs; lia|].
          apply Forall_cons; [cbn [kentry_ok]; evs; rewrite ?u64_of_Z by lia; lia|].
          apply Forall_cons; [|apply Forall_nil].
          unfold sh0, shk in SH. replace ((TSW + 8 * x) / 8 + SHBASE) with (x + 2147646820) in SH
            by (unfold TSW, SHBASE; clear; Z.div_mod_to_equations; lia).
          cbn [kentry_ok]. split; [lia|]. split.
          - unfold flat, estart. cbn [a_base a_off]. evs. rewrite u64_of_Z by lia. lia.
          - unfold adenot. cbn [a_base a_off]. evs. rewrite v_addi_Z by lia. rewrite word_to_le_bytes_1 by lia. exact SH. }
        change (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AT_OPERAND_TYPE_STR) fc None m (seg_rom asegs))
          with (@PropExec.mkst (PropExec.mkFP F fc) (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   (Z_to_bv 64 AT_OPERAND_TYPE_STR) m (seg_rom asegs)).
        xrun_at (PropExec.mkFP F fc) asegs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          AT_OPERAND_TYPE_STR m (seg_rom asegs) HR HK 40%nat [TS_RET1] ACC_SCR 37%N.
        { split_scs.
          all: eapply (sc_read_cellw asegs _ _ _ (TSW + 8 * x) 8%N (tstr_ptr x)); [exact CELL | lia | | subst E; evs; reflexivity].
          all: subst E; unfold adenot; cbn [a_base a_off]; evs.
          all: rewrite TablLib.zbv_mul, v_addi_Z by (unfold TSW; lia); f_equal; unfold TSW; lia. }
        lazymatch type of Hlf with log_flat _ ?lg =>
          lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
            change mm with (mem_denot E m lg) in Hms end end.
        eexists R', _. split; [exact Hms|]. split; [exact Hlf|]. split; [vm_cast_no_check (@eq_refl bool true)|].
        subst E.
        split; [intros rr Hrr; eapply (syms_id_sound _ _ _ R' KCS HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
        rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 10%bv G10.
        split; [exact G1|]. split; [exact G2|]. exact G10. }
      eapply evt_of_msteps; [exact MS|].
      step.
      apply evt_done.
      exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
        (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), M1.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact AC1|].
      exists (tstr_ptr x), (snd (nth (Z.to_nat x) TSTR_A (0, 0))).
      split; [exact (tstrA_facts _ (tstr_ptr_in x ltac:(lia)))|]. split; [exact P10|].
      unfold tstrA_of, tstr_ptr. destruct (Z.leb_spec 0 x); [|lia]. destruct (Z.ltb_spec x 108); [|lia]. cbn [andb].
      change (ti_tstr tiA) with TSTR_A. rewrite <- surjective_pairing. reflexivity.
  Qed.
End TS.
