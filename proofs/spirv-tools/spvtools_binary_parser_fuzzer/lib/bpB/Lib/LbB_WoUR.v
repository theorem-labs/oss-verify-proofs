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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_WoR2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoBP.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS11_RA : Z := 0xec194.
Definition WO_MS12_RA : Z := 0xec1a8.
Definition WO_MS13_RA : Z := 0xec1c0.
Definition WO_MS14_RA : Z := 0xec1d4.
Definition WO_MS15_RA : Z := 0xec1f4.

Section WoUR.
  Context {HCEIL : HeapCeil}.

  Definition wu1_post (gp tp s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff r lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS11_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 0) (Z_to_bv 64 46) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3104)) s6 s7 (Z_to_bv 64 r)
                    s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 382, sh ff + 412)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ u8arr asegs m1 (sh ff) (map (Z_to_bv 8) (wo_sh [19; 20; 21]%nat)).

  Lemma wu1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s5 s6 s7 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff r lo : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 -> (sh ff + 512 <= ff \/ ff + 4096 <= sh ff) ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (ff + 2224))] ->
    u8arr asegs m (sh ff) (map (Z_to_bv 8) (wo_sh [20; 21]%nat)) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wu1_post gp tp s6 s7 s9 s10 s11 F fc SP S1 ff r lo m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 BP_WCF) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 FSH C48 US ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 2 ^ 45)
      by (clear - FLO FS1 S1L S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    assert (WS : wr_at asegs m (sh ff) 476).
    { destruct US as (_ & (W1 & W2 & W)). rewrite length_map in W2, W. cbn [length wo_sh wo_sh_go WO_OBJS app repeat existsb Nat.eqb] in W2, W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP; Z_to_bv 64 r]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34); (8%bv, EVar 35); (2%bv, EVar 34); (24%bv, EVar 36);
                   (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (20%bv, EMd M_MUL (ELit 64) (EVar 32))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]. rewrite QS, w_add by lia. f_equal. lia. }
    assert (ESb : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - 0x7fff8000)
      by (evs; rewrite QS, u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 48) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 2224));
        KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 476);
        KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 0%nat (C8 (Z_to_bv 64 (ff + 2224)))); [exact C48 | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ES', u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R BP_WCF m (seg_rom asegs) HR HK 100%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 24%bv L24.
    assert (L1' : getr R' 1 = Z_to_bv 64 WO_MS11_RA) by (rewrite L1; reflexivity).
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; reflexivity).
    assert (L8' : getr R' 8 = Z_to_bv 64 SP) by (rewrite L8; reflexivity).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 3056)) by (rewrite L10, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L18' : getr R' 18 = Z_to_bv 64 (ff + 3056)) by (rewrite L18, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by (rewrite L19, QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia).
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by (rewrite L20; exact Q).
    assert (L21' : getr R' 21 = Z_to_bv 64 (ff + 3104)) by (rewrite L21, Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity).
    assert (L24' : getr R' 24 = Z_to_bv 64 r) by (rewrite L24; reflexivity).
    assert (MU1 : munch [(sh ff + 382, sh ff + 412)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE; lia|]).
      apply Forall_nil. }
    assert (US1 : u8arr asegs M1 (sh ff) (map (Z_to_bv 8) (wo_sh [19; 20; 21]%nat))).
    { subst M1. lazymatch type of ESb with bv_unsigned ?t = _ => replace (sh ff) with (bv_unsigned t + SHBASE) by (rewrite ESb; unfold SHBASE; lia) end.
      lazymatch type of Hlf with log_flat _ ?lg =>
        let l := eval vm_compute in (others (EMd M_MUL (ELit 8) (EVar 32)) lg) in
        assert (HO : others (EMd M_MUL (ELit 8) (EVar 32)) lg = l) by (vm_cast_no_check (@eq_refl _ l)) end.
      eapply u8arr_mem_denot with (base := wo_sh [20; 21]%nat);
        [exact Hlf | | rewrite ESb; unfold SHBASE; lia | rewrite ESb; unfold SHBASE; cbn [length wo_sh wo_sh_go WO_OBJS app repeat existsb Nat.eqb]; lia
        | rewrite ESb; replace (sh ff - 0x7fff8000 + SHBASE) with (sh ff) by (unfold SHBASE; lia); exact US
        | vm_cast_no_check (@eq_refl _ (Some (wo_sh [19; 20; 21]%nat)))].
      intros i Hi. cbn [length wo_sh wo_sh_go WO_OBJS app repeat existsb Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in Hi.
      apply (lmiss_of_others _ _ _ _ 476); [| lia]. rewrite HO.
      clear - ES' EF' SHB FSH SHL F64 FLO FS1 S1L S1H SPH.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11, L12, L18', L19', L20', L21', L24'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST | exact US1].
  Qed.

  Ltac wu_setup ff Q QS SHL EF' ES' :=
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia);
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia);
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 2 ^ 45)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia);
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity);
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).

  Ltac wu_regs ff Q QS :=
    apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
    match goal with HR0 : _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => subst end; evs;
    try reflexivity; try (rewrite Q; reflexivity);
    first [ transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]; rewrite QS, w_add by lia; f_equal; lia
          | match goal with |- getr _ _ = alu64 ALU_ADD (mul_div _ _ _) (Z_to_bv 64 ?k) =>
              transitivity (Z_to_bv 64 (ff + k)); [reflexivity|]; rewrite Q, w_add by lia; reflexivity end ].

  Ltac wu_reg_eq Q QS L :=
    rewrite L; first [ reflexivity | rewrite Q; reflexivity | rewrite Q; rewrite ?w_add, ?v_addi_Z by lia; reflexivity
                     | rewrite QS; rewrite ?w_add, ?w_addm by lia; f_equal; lia ].

  Definition wu2_post (gp tp s2 s6 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
      ms' = MS (mkR (Z_to_bv 64 WO_MS12_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 3104)) (Z_to_bv 64 0) (Z_to_bv 64 32) x13 x14 x15 x16 x17
                    s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3104)) s6 s7 s8 s9 (Z_to_bv 64 32) s11 x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m (seg_rom asegs).
  Lemma wu2 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 ->
    evt asegs (wu2_post gp tp s2 s6 s7 s8 s9 s11 F fc SP S1 ff m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3104)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS11_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until ff. intros S1L S1H SPH F64 FLO FS1.
    wu_setup ff Q QS SHL EF' ES'.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3104)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34); (8%bv, EVar 35); (2%bv, EVar 34);
                   (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (20%bv, EMd M_MUL (ELit 64) (EVar 32));
                   (21%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3104))]) R) by wu_regs ff Q QS.
    assert (HK : know_ok asegs E m [ KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS11_RA m (seg_rom asegs) HR HK 40%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs]. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 26%bv L26.
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 3104)) by wu_reg_eq Q QS L10.
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by wu_reg_eq Q QS L20.
    assert (L21' : getr R' 21 = Z_to_bv 64 (ff + 3104)) by wu_reg_eq Q QS L21.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L2, L8, L9, L10', L11, L12, L19', L20', L21', L26.
    apply evt_done.
    do 12 eexists. reflexivity.
  Qed.

  Definition wu3_post (gp tp s6 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS13_RA) (Z_to_bv 64 S1) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ff + 3144)) (Z_to_bv 64 0) (Z_to_bv 64 32) y13 y14 y15 y16 y17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 (Z_to_bv 64 32) s11 y28 y29 y30 y31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3136, ff + 3140)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (ff + 3136) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wu3 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5 s6 s7 s8 s9 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 ->
    wr_at asegs m (ff + 3056) 240 -> mem_inv asegs m ->
    evt asegs (wu3_post gp tp s6 s7 s8 s9 s11 F fc SP S1 ff m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 s8 s9 (Z_to_bv 64 32) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS12_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until ff. intros S1L S1H SPH F64 FLO FS1 WT MI.
    wu_setup ff Q QS SHL EF' ES'.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 s8 s9 (Z_to_bv 64 32) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3056)); (26%bv, ELit 32)]) R) by wu_regs ff Q QS.
    assert (HK : know_ok asegs E m [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 3056) (ELit 240); KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WT | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS12_RA m (seg_rom asegs) HR HK 40%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs]. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 8%bv L8.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 12%bv L12.
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 26%bv L26.
    assert (L1' : getr R' 1 = (Z_to_bv 64 WO_MS13_RA)) by wu_reg_eq Q QS L1.
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L2.
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by wu_reg_eq Q QS L8.
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L9.
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 3144))) by wu_reg_eq Q QS L10.
    assert (L11' : getr R' 11 = (Z_to_bv 64 0)) by wu_reg_eq Q QS L11.
    assert (L12' : getr R' 12 = (Z_to_bv 64 32)) by wu_reg_eq Q QS L12.
    assert (L18' : getr R' 18 = (Z_to_bv 64 (ff + 3056))) by wu_reg_eq Q QS L18.
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff))) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by wu_reg_eq Q QS L20.
    assert (L21' : getr R' 21 = (Z_to_bv 64 0x3f800000)) by wu_reg_eq Q QS L21.
    assert (L26' : getr R' 26 = (Z_to_bv 64 32)) by wu_reg_eq Q QS L26.
    assert (MU1 : munch [(ff + 3136, ff + 3140)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT' : forall a n, ff + 3056 <= a -> a + n <= ff + 3296 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WT as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 3056 + (a - (ff + 3056) + i)) by lia. apply W. lia. }
    assert (CT1 : rw_cells asegs M1 (ff + 3136) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHL F64 FLO FS1 S1L S1H SPH WT' Q.
      lgc Hlf 0%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia);
        first [apply WT'; cbn; lia | HLib.evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L12', L18', L19', L20', L21', L26'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI) | exact CT1].
  Qed.

  Definition wu4_post (gp tp s6 s7 s8 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS14_RA) (Z_to_bv 64 S1) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ff + 3184)) (Z_to_bv 64 0) (Z_to_bv 64 32) y13 y14 y15 y16 y17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 (Z_to_bv 64 32) s11 y28 y29 y30 y31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3176, ff + 3180)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (ff + 3176) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wu4 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s6 s7 s8 s9 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 ->
    wr_at asegs m (ff + 3056) 240 -> mem_inv asegs m ->
    evt asegs (wu4_post gp tp s6 s7 s8 s9 s11 F fc SP S1 ff m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 (Z_to_bv 64 32) s11 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS13_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until ff. intros S1L S1H SPH F64 FLO FS1 WT MI.
    wu_setup ff Q QS SHL EF' ES'.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 (Z_to_bv 64 32) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3056)); (21%bv, ELit 1065353216); (26%bv, ELit 32)]) R) by wu_regs ff Q QS.
    assert (HK : know_ok asegs E m [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 3056) (ELit 240); KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WT | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS13_RA m (seg_rom asegs) HR HK 40%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs]. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 8%bv L8.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 12%bv L12.
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 26%bv L26.
    assert (L1' : getr R' 1 = (Z_to_bv 64 WO_MS14_RA)) by wu_reg_eq Q QS L1.
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L2.
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by wu_reg_eq Q QS L8.
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L9.
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 3184))) by wu_reg_eq Q QS L10.
    assert (L11' : getr R' 11 = (Z_to_bv 64 0)) by wu_reg_eq Q QS L11.
    assert (L12' : getr R' 12 = (Z_to_bv 64 32)) by wu_reg_eq Q QS L12.
    assert (L18' : getr R' 18 = (Z_to_bv 64 (ff + 3056))) by wu_reg_eq Q QS L18.
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff))) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by wu_reg_eq Q QS L20.
    assert (L21' : getr R' 21 = (Z_to_bv 64 0x3f800000)) by wu_reg_eq Q QS L21.
    assert (L26' : getr R' 26 = (Z_to_bv 64 32)) by wu_reg_eq Q QS L26.
    assert (MU1 : munch [(ff + 3176, ff + 3180)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT' : forall a n, ff + 3056 <= a -> a + n <= ff + 3296 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WT as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 3056 + (a - (ff + 3056) + i)) by lia. apply W. lia. }
    assert (CT1 : rw_cells asegs M1 (ff + 3176) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHL F64 FLO FS1 S1L S1H SPH WT' Q.
      lgc Hlf 0%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia);
        first [apply WT'; cbn; lia | HLib.evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L12', L18', L19', L20', L21', L26'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI) | exact CT1].
  Qed.

  Definition wu5_post (gp tp s6 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS15_RA) (Z_to_bv 64 S1) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 0) (Z_to_bv 64 72) y13 y14 y15 y16 y17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) s6 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11 y28 y29 y30 y31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3216, ff + 3220)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (ff + 3216) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wu5 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 ->
    wr_at asegs m (ff + 3056) 240 -> mem_inv asegs m ->
    evt asegs (wu5_post gp tp s6 s8 s10 s11 F fc SP S1 ff m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS14_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until ff. intros S1L S1H SPH F64 FLO FS1 WT MI.
    wu_setup ff Q QS SHL EF' ES'.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (18%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3056)); (21%bv, ELit 1065353216)]) R) by wu_regs ff Q QS.
    assert (HK : know_ok asegs E m [ KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 3056) (ELit 240); KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WT | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS14_RA m (seg_rom asegs) HR HK 40%nat [AASAN_MEMSET] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs]. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 8%bv L8.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 12%bv L12.
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 23%bv L23.
    rreg HR' 25%bv L25.
    assert (L1' : getr R' 1 = (Z_to_bv 64 WO_MS15_RA)) by wu_reg_eq Q QS L1.
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L2.
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by wu_reg_eq Q QS L8.
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L9.
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 3224))) by wu_reg_eq Q QS L10.
    assert (L11' : getr R' 11 = (Z_to_bv 64 0)) by wu_reg_eq Q QS L11.
    assert (L12' : getr R' 12 = (Z_to_bv 64 72)) by wu_reg_eq Q QS L12.
    assert (L18' : getr R' 18 = (Z_to_bv 64 (ff + 3056))) by wu_reg_eq Q QS L18.
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff))) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by wu_reg_eq Q QS L20.
    assert (L21' : getr R' 21 = (Z_to_bv 64 (ff + 3224))) by wu_reg_eq Q QS L21.
    assert (L23' : getr R' 23 = (Z_to_bv 64 (ff + 3248))) by wu_reg_eq Q QS L23.
    assert (L25' : getr R' 25 = (Z_to_bv 64 (ff + 3272))) by wu_reg_eq Q QS L25.
    assert (MU1 : munch [(ff + 3216, ff + 3220)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WT' : forall a n, ff + 3056 <= a -> a + n <= ff + 3296 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WT as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 3056 + (a - (ff + 3056) + i)) by lia. apply W. lia. }
    assert (CT1 : rw_cells asegs M1 (ff + 3216) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. clear - Hlf EF' ES' SHL F64 FLO FS1 S1L S1H SPH WT' Q.
      lgc Hlf 0%nat ltac:(cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; lia);
        first [apply WT'; cbn; lia | HLib.evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L12', L18', L19', L20', L21', L23', L25'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI) | exact CT1].
  Qed.

  Definition wu6_post (gp tp s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 y12,
      ms' = MS (mkR (Z_to_bv 64 0xec200) (Z_to_bv 64 S1) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 25) y12 y13 y14 y15 y16 y17 s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
               F (Z_to_bv 64 0xec4ac) fc None m (seg_rom asegs).
  Lemma wu6 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 ->
    evt asegs (wu6_post gp tp s2 s6 s7 s8 s9 s10 s11 F fc SP S1 ff m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS15_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until ff. intros S1L S1H SPH F64 FLO FS1.
    wu_setup ff Q QS SHL EF' ES'.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 34); (8%bv, EVar 35); (9%bv, EVar 34); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3224))]) R) by wu_regs ff Q QS.
    assert (HK : know_ok asegs E m [ KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS15_RA m (seg_rom asegs) HR HK 40%nat [0xec4ac] (SCR [] [] []) 60%N.
    { first [apply Forall_nil | split_scs]. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 8%bv L8.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    assert (L1' : getr R' 1 = (Z_to_bv 64 0xec200)) by wu_reg_eq Q QS L1.
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L2.
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by wu_reg_eq Q QS L8.
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by wu_reg_eq Q QS L9.
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 3224))) by wu_reg_eq Q QS L10.
    assert (L11' : getr R' 11 = (Z_to_bv 64 25)) by wu_reg_eq Q QS L11.
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff))) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by wu_reg_eq Q QS L20.
    assert (L21' : getr R' 21 = (Z_to_bv 64 (ff + 3224))) by wu_reg_eq Q QS L21.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L19', L20', L21'.
    apply evt_done.
    do 13 eexists. reflexivity.
  Qed.

  Definition we1_post (gp tp s5 s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff r lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 0xec3d8) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 ff) (Z_to_bv 64 3808) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 AFS_FREE_6) fc None m1 (seg_rom asegs)
      /\ munch [(ff, ff + 8); (sh ff + 420, sh ff + 428); (sh ff + 432, sh ff + 468)] m m1 /\ wmono asegs m m1
      /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.

  Lemma we1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s5 s6 s7 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff r lo : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 4096 <= S1 -> (sh ff + 512 <= ff \/ ff + 4096 <= sh ff) ->
    rw_cells asegs m S1 [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)] ->
    rw_cells asegs m (S1 + 40) [C8 (Z_to_bv 64 0x7fff8000)] ->
    rw_cells asegs m (S1 + 56) [C8 (Z_to_bv 64 (ff + 3376))] ->
    rw_cells asegs m (ff + 3408) [C8 (Z_to_bv 64 0)] ->
    wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 476 ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (we1_post gp tp s5 s6 s7 s9 s10 s11 F fc SP S1 ff r lo m)
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xec2b0) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 FSH C0 C40 C56 C3408 WF WS ST MI.
    wu_setup ff Q QS SHL EF' ES'.
    assert (C0' : rw_cells asegs m (S1 + 0) [C8 (Z_to_bv 64 (ff + 3360))])
      by (rewrite Z.add_0_r; change [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)] with ([C8 (Z_to_bv 64 (ff + 3360))] ++ [C8 (Z_to_bv 64 ff)]) in C0;
          apply rw_cells_app in C0 as [X _]; exact X).
    assert (C8' : rw_cells asegs m (S1 + 8) [C8 (Z_to_bv 64 ff)]).
    { change [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)] with ([C8 (Z_to_bv 64 (ff + 3360))] ++ [C8 (Z_to_bv 64 ff)]) in C0.
      apply rw_cells_app in C0 as [_ X]. cbn [cells_size csize] in X. replace (S1 + 8) with (S1 + Z.of_nat 8) by lia. exact X. }
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 SP; Z_to_bv 64 r]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34); (8%bv, EVar 35); (2%bv, EVar 34); (24%bv, EVar 36);
                   (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                   (20%bv, EMd M_MUL (ELit 64) (EVar 32))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      transitivity (Z_to_bv 64 (sh ff)); [reflexivity|]. rewrite QS, w_add by lia. f_equal. lia. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 34) 0) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3360));
        KWord (SA (EVar 34) 8) 8 (EMd M_MUL (ELit 64) (EVar 32));
        KWord (SA (EVar 34) 40) 8 (ELit 2147450880);
        KWord (SA (EVar 34) 56) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3376));
        KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 3408) 8 (ELit 0);
        KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
        KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 476);
        KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41);
        KRange (EVar 34) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 0) _ 0%nat (C8 (Z_to_bv 64 (ff + 3360)))); [exact C0' | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 8) _ 0%nat (C8 (Z_to_bv 64 ff))); [exact C8' | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 40) _ 0%nat (C8 (Z_to_bv 64 0x7fff8000))); [exact C40 | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 56) _ 0%nat (C8 (Z_to_bv 64 (ff + 3376)))); [exact C56 | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 3408) _ 0%nat (C8 (Z_to_bv 64 0))); [exact C3408 | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite ES', u64_of_Z by lia; unfold SHBASE; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xec2b0 m (seg_rom asegs) HR HK 120%nat [AFS_FREE_6] (SCR [] [] []) 60%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 24%bv L24.
    assert (L1' : getr R' 1 = Z_to_bv 64 0xec3d8) by wu_reg_eq Q QS L1.
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by wu_reg_eq Q QS L2.
    assert (L8' : getr R' 8 = Z_to_bv 64 SP) by wu_reg_eq Q QS L8.
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by wu_reg_eq Q QS L9.
    assert (L10' : getr R' 10 = Z_to_bv 64 ff) by wu_reg_eq Q QS L10.
    assert (L11' : getr R' 11 = Z_to_bv 64 3808) by wu_reg_eq Q QS L11.
    assert (L18' : getr R' 18 = Z_to_bv 64 ff) by wu_reg_eq Q QS L18.
    assert (L19' : getr R' 19 = Z_to_bv 64 (sh ff)) by wu_reg_eq Q QS L19.
    assert (L20' : getr R' 20 = Z_to_bv 64 ff) by wu_reg_eq Q QS L20.
    assert (L24' : getr R' 24 = Z_to_bv 64 r) by wu_reg_eq Q QS L24.
    assert (MU1 : munch [(ff, ff + 8); (sh ff + 420, sh ff + 428); (sh ff + 432, sh ff + 468)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L18', L19', L20', L24'.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

End WoUR.
