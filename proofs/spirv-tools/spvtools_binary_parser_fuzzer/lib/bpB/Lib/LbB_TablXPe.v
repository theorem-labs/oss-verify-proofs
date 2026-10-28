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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_DStat LbB_RGb2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_ContStmt LbB_ContVot LbB_RGl LbB_TablStmt LbB_TablOS1 LbB_TablPT1 LbB_TablPT4 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition xp_disp_pc (t : Z) : Z :=
  if t =? 106 then xs_pc K1 else if t =? 52 then xs_pc K5 else if t =? 53 then xs_pc K2
  else if t =? 54 then xs_pc K3 else if t =? 55 then xs_pc K4 else XP_EXIT.

Definition KDP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Definition KB2 : list reg := [1; 3; 4; 22; 23; 24]%bv.

Lemma xp_br_ge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
  intros x y Hx Hy. pose proof (br_lts_small x y Hx Hy) as H. cbn [branch_taken] in H |- *. rewrite H. reflexivity.
Qed.

Section XPe.
  Context {HCEIL : HeapCeil}.

  Definition xp1_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SP S1 t v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 XP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 160)
                    x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 v) s4 (Z_to_bv 64 t) s6 s7 s8 s9 s10 (Z_to_bv 64 0x7fff8000)
                    x28 x29 x30 x31) F (Z_to_bv 64 AFS_MALLOC_2) fc None m1 (seg_rom asegs)
      /\ munch [(SP - 160, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma xp_b1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (t v lo : Z),
    a0 = Z_to_bv 64 t -> 0 <= t < 2 ^ 64 -> a1 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 256 ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (xp1_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp)
                 (bv_unsigned sp - 160 - (bv_unsigned sp - 160) mod 32) t v lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_EXPAND) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t v lo
    Ha0 TR Ha1 VR SP16 SPR ST CE LOS MI AC.
  set (SP := bv_unsigned sp) in *.
  assert (Hsp : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
  remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
  pose (E := Eseed R [Z_to_bv 64 SP; Z_to_bv 64 t; Z_to_bv 64 v]).
  assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33); (11%bv, EVar 34)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|].
    repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; first [exact Hsp | exact Ha0 | exact Ha1]. }
  assert (EP : bv_unsigned (edenot E (EVar 32)) = SP) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
  pose proof (ACONST_shbase m AC) as [CG CS].
  pose proof (ACONST_uar m AC) as [CU CF].
  assert (HK : know_ok asegs E m
     [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
       KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
       KWord (SA (ELit 0) AGOT_UAR) 8 (ELit AUAR_CELL);
       KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
       KWr (SA (EVar 32) (-160)) (ELit 160);
       KRange (EVar 32) (2 ^ 45) (2 ^ 47); KAlign (EVar 32) 16 ]).
  { unfold know_ok.
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL)));
        [exact CG | reflexivity | reflexivity | lia | reflexivity | cbv [AGOT_SHBASE]; lia | cbv [AGOT_SHBASE]; cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz ASHADOW_BASE)));
        [exact CS | reflexivity | reflexivity | lia | reflexivity | cbv [ASHBASE_CELL]; lia | cbv [ASHBASE_CELL]; cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m AGOT_UAR _ 0%nat (C8 (wz AUAR_CELL)));
        [exact CU | reflexivity | reflexivity | lia | reflexivity | cbv [AGOT_UAR]; lia | cbv [AGOT_UAR]; cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_rw_cells asegs E m AUAR_CELL _ 0%nat (C4 (wz 1)));
        [exact CF | reflexivity | reflexivity | lia | reflexivity | cbv [AUAR_CELL]; lia | cbv [AUAR_CELL]; cbn; lia | reflexivity]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                         | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; subst E; evs; rewrite u64_of_Z by lia; lia
                         | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R AT_EXPAND m (seg_rom asegs) HR HK 300%nat [AFS_MALLOC_2] (SCR [] [] []) 60%N.
  { first [apply Forall_nil | split_scs]. }
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
  pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
  readback HR' HF1 HR0 HRe.
  rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10.
  rreg HR' 19%bv L19. rreg HR' 21%bv L21. rreg HR' 27%bv L27.
  assert (S1E : alu64 ALU_ADD (Z_to_bv 64 SP) (Z_to_bv 64 (-160)) = Z_to_bv 64 (SP - 160)) by (rewrite w_addm by lia; f_equal; lia).
  assert (S1Q : mul_div M_MUL (Z_to_bv 64 32) (alu64 ALU_SRL (Z_to_bv 64 (SP - 160)) (Z_to_bv 64 5))
                = Z_to_bv 64 (SP - 160 - (SP - 160) mod 32)).
  { rewrite TablLib.w_srl by lia. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal. Z.div_mod_to_equations; lia. }
  rewrite S1E, S1Q in L2, L9.
  assert (MU1 : munch [(SP - 160, SP)] m M1).
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EP;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil. }
  Ltac xcell Hlf EP ST HR0 k :=
    eapply (rw_cells_log_nth_sb _ _ _ k);
    [ exact Hlf | reflexivity | reflexivity | rewrite EP; lia
    | eapply wr_at_sub; [exact (wr_at_of_stk _ _ _ _ ST) | lia | cbn; lia | cbn; lia]
    | reflexivity | exact I | rewrite HR0; evs; reflexivity ].
  assert (CSV : rw_cells asegs M1 (SP - 104)
                  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { subst M1.
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 0%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 1%nat|].
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 2%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 3%nat|].
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 4%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 5%nat|].
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 6%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 7%nat|].
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 8%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 9%nat|].
    apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 10%nat|]. apply rw_cells_cons8_c; [xcell Hlf EP ST HR0 11%nat|].
    xcell Hlf EP ST HR0 12%nat. }
  eapply evt_of_msteps; [exact Hms|].
  rewrite mkst_MS, HRe, L1, L2, L8, L9, L10, L19, L21, L27.
  apply evt_done.
  unfold xp1_post. do 14 eexists. exists M1. split; [reflexivity|].
  split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  split; [subst M1; apply stk_mem_denot; exact ST|].
  exact CSV.
Qed.

  Lemma xp_b2 : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff SP S1 v t lo : Z),
    getr R 10 = Z_to_bv 64 ff -> getr R 9 = Z_to_bv 64 S1 -> getr R 2 = Z_to_bv 64 S1 -> getr R 8 = Z_to_bv 64 SP ->
    getr R 19 = Z_to_bv 64 v -> getr R 21 = Z_to_bv 64 t -> getr R 27 = Z_to_bv 64 0x7fff8000 -> rfull R ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 256 <= 2 ^ 47 -> (ff + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0 <= t < 2 ^ 31 -> 0 <= v < 2 ^ 64 ->
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 160 <= SP -> SP <= 2 ^ 47 ->
    wr_at asegs m ff 256 -> wr_at asegs m (sh ff) 32 -> stk asegs m lo SP -> lo <= S1 -> ff + 256 <= lo ->
    relro0 m -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 XP_SM_RET) fc None m ro) (MS R' F (Z_to_bv 64 XP_DISP) fc None M' ro)
      /\ rfull R' /\ kept_in KB2 R R'
      /\ getr R' 2 = Z_to_bv 64 S1 /\ getr R' 8 = Z_to_bv 64 SP /\ getr R' 9 = Z_to_bv 64 S1 /\ getr R' 10 = Z_to_bv 64 0
      /\ getr R' 11 = Z_to_bv 64 53 /\ getr R' 18 = Z_to_bv 64 ff /\ getr R' 19 = Z_to_bv 64 v /\ getr R' 20 = Z_to_bv 64 (ff + 32)
      /\ getr R' 21 = Z_to_bv 64 t /\ getr R' 25 = Z_to_bv 64 (sh ff) /\ getr R' 26 = Z_to_bv 64 ff /\ getr R' 27 = Z_to_bv 64 0x7fff8000
      /\ munch [(S1 + 48, S1 + 56); (ff, ff + 24); (sh ff, sh ff + 20); (ff + 32, ff + 36)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo' hi', stk asegs m lo' hi' -> stk asegs M' lo' hi')
      /\ rw_cells asegs M' (ff + 32) [C4 (Z_to_bv 64 t)]
      /\ rw_cells asegs M' (sh ff + 4) [C1 (b8 4)].
Proof.
  intros R F fc m ro ff SP S1 v t lo P10 P9 P2 P8 P19 P21 P27 HF F64 FLO FHI FB TR VR S32 S45 SS SPH WF WS ST LO FLOW RR MI.
  assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
  assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
  assert (DJ : ff + 256 <= 8 * (ff / 64) + SHBASE \/ 8 * (ff / 64) + SHBASE + 32 <= ff)
    by (unfold SHBASE; Z.div_mod_to_equations; lia).
  assert (FQ : 0x6e8000 / 64 <= ff / 64 <= 2 ^ 41) by (Z.div_mod_to_equations; lia).
  pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 v; Z_to_bv 64 t; Z_to_bv 64 SP]).
  assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 64) (EVar 32)); (9%bv, EVar 33); (2%bv, EVar 33); (8%bv, EVar 36);
                                     (19%bv, EVar 34); (21%bv, EVar 35); (27%bv, ELit SHBASE)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|].
    repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
      first [rewrite Q; exact P10 | exact P9 | exact P2 | exact P8 | exact P19 | exact P21 | exact P27]. }
  assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (subst E; evs; rewrite Q, u64_of_Z by lia; reflexivity).
  assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
    by (subst E; evs; rewrite w_mul by lia; rewrite u64_of_Z by lia; reflexivity).
  assert (E33 : bv_unsigned (edenot E (EVar 33)) = S1) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
  assert (E35 : bv_unsigned (edenot E (EVar 35)) = t) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
  assert (E36 : bv_unsigned (edenot E (EVar 36)) = SP) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
  assert (HK : know_ok asegs E m
     [ KImg 0x17e000 0x186000;
       KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 256);
       KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 32);
       KWr (SA (EVar 33) 48) (ELit 8);
       KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41); KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 35) 0 (2 ^ 31 - 1);
       KRange (EVar 36) (2 ^ 45) (2 ^ 47) ]).
  { unfold know_ok.
    apply Forall_cons. { apply kimg_relro. exact RR. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; subst E; evs; rewrite u64_of_Z by lia; lia
                           | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; subst E; evs; rewrite u64_of_Z by lia; lia
                           | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E33; lia
                         | unfold estart, elenZ; cbn [a_base a_off]; rewrite E33; subst E; evs; rewrite u64_of_Z by lia; lia
                         | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons. { cbn [kentry_ok]. subst E; evs. rewrite u64_of_Z by lia. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite E33. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite E35. lia. }
    apply Forall_cons. { cbn [kentry_ok]. rewrite E36. lia. }
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R XP_SM_RET m ro HR HK 300%nat [XP_DISP] (SCR [] [] []) 60%N.
  { first [apply Forall_nil | split_scs]. }
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
  exists R', M1. split; [exact Hms|].
  split; [exact (msteps_full asegs _ _ Hms HF)|].
  split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KB2 HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
  rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 18%bv L18.
  rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 25%bv L25. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
  rewrite Q in L18, L20, L26. rewrite w_add in L20 by lia.
  rewrite w_mul in L25 by lia. rewrite w_add in L25 by (unfold SHBASE in *; lia).
  assert (L25' : getr R' 25 = Z_to_bv 64 (sh ff)) by (rewrite L25; f_equal; unfold SHBASE in QS; lia).
  split; [exact L2|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact L11|]. split; [exact L18|].
  split; [exact L19|]. split; [exact L20|]. split; [exact L21|]. split; [exact L25'|]. split; [exact L26|]. split; [exact L27|].
  split.
  { subst M1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                first [rewrite EF | rewrite ES | rewrite E33];
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
    apply Forall_nil. }
  split; [subst M1; apply wmono_mem_denot|].
  split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
  split; [intros lo' hi' S'; subst M1; apply stk_mem_denot; exact S'|].
  split.
  { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
      | unfold estart; cbn [a_base a_off]; rewrite EF; reflexivity | eapply wr_at_sub; [exact WF | lia | cbn; lia | cbn; lia]
      | reflexivity | exact I | evs; reflexivity]. }
  subst M1. eapply (rw_cells_log_nth _ m _ 16%nat); [exact Hlf | reflexivity | | | | reflexivity | exact I | reflexivity].
  - cbn [firstn].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite ?EF, ?ES;
                                cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
    apply Forall_nil.
  - unfold estart; cbn [a_base a_off]; rewrite ES. unfold SHBASE in *. lia.
  - eapply wr_at_sub; [exact WS | lia | cbn; lia | cbn; lia].
Qed.

  Lemma xp_disp : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (t : Z),
    getr R 21 = Z_to_bv 64 t -> getr R 11 = Z_to_bv 64 53 -> 0 <= t < 2 ^ 31 -> rfull R ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 XP_DISP) fc None m ro) (MS R' F (Z_to_bv 64 (xp_disp_pc t)) fc None m ro)
      /\ rfull R' /\ kept_in KDP R R'.
Proof.
Ltac drun R F fc m ro HR HK HF tgt scr :=
      xrun_at (PropExec.mkFP F fc) asegs R XP_DISP m ro HR HK 20%nat [tgt] scr 40%N;
      [ first [apply Forall_nil | split_scs];
        cbn [sc_denot]; HLib.evs; first [rewrite br_eq by lia | rewrite br_ne by lia | rewrite xp_br_ge by lia];
        first [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia
              | rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity | ];
      lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R' _ ?mm _) |- _ =>
        change mm with m in Hms;
        exists R'; split; [exact Hms|];
        split; [exact (msteps_full asegs _ _ Hms HF)|]
      end.
Ltac dkept R R' HR' := intros rr Hrr; eapply (syms_id_sound R _ _ R' KDP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
  intros R F fc m ro t H21 H11 HT HF.
  pose (E := Eseed R [Z_to_bv 64 t]).
  assert (HR : regs_ok E (srs sr_id [(21%bv, EVar 32); (11%bv, ELit 53)]) R).
  { apply regs_ok_srs; [apply regs_ok_seed|].
    repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs; assumption. }
  assert (HK : know_ok asegs E m [KRange (EVar 32) 0 (2 ^ 31 - 1)]).
  { apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. subst E; evs. rewrite u64_of_Z by lia. lia. }
  unfold xp_disp_pc.
  destruct (Z.eqb_spec t 106) as [T106|T106].
  { drun R F fc m ro HR HK HF (xs_pc K1) (SCR [false; false; false; false] [] []). dkept R R' HR'. }
  destruct (Z.eqb_spec t 52) as [T52|T52].
  { drun R F fc m ro HR HK HF (xs_pc K5) (SCR [true; true] [] []). dkept R R' HR'. }
  destruct (Z.eqb_spec t 53) as [T53|T53].
  { drun R F fc m ro HR HK HF (xs_pc K2) (SCR [true; false; false] [] []). dkept R R' HR'. }
  destruct (Z.eqb_spec t 54) as [T54|T54].
  { drun R F fc m ro HR HK HF (xs_pc K3) (SCR [false; true] [] []). dkept R R' HR'. }
  destruct (Z.eqb_spec t 55) as [T55|T55].
  { drun R F fc m ro HR HK HF (xs_pc K4) (SCR [false; false; true] [] []). dkept R R' HR'. }
  destruct (Z.le_gt_cases t 53) as [TL|TL].
  { drun R F fc m ro HR HK HF XP_EXIT (SCR [true; false; true] [] []). dkept R R' HR'. }
  drun R F fc m ro HR HK HF XP_EXIT (SCR [false; false; false; true] [] []). dkept R R' HR'.
Qed.
End XPe.
