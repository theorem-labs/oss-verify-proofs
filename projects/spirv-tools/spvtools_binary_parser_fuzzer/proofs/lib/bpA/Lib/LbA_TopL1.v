(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_RGl.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition LP_HEAD : Z := 0xe8e48.
Definition LP_EXIT : Z := 0xe8f2c.

Definition KSL : list reg := [1; 2; 3; 4; 7; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.

Lemma kbyte : forall E M (e ez : expr) (c j z : Z),
  edenot E e = Z_to_bv 64 c -> edenot E ez = Z_to_bv 64 z -> 0 <= c -> 0 <= j -> c + j + 1 < 2 ^ 64 ->
  rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z] -> 0 <= z < 256 ->
  kentry_ok asegs E M (KWord (SA e j) 1 ez).
Proof.
  intros E M e ez c j z Ec Ez Hc Hj Hcj HZ Hz.
  cbn [kentry_ok]. split; [lia|]. split.
  - unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite Ec, u64_of_Z by lia. lia.
  - unfold adenot. cbn [a_base a_off]. rewrite Ec. rewrite v_addi_Z by lia.
    rewrite rdn_HL, HZ, Ez. rewrite word_to_le_bytes_1 by lia. reflexivity.
Qed.

Lemma srl2_val : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 2) = Z_to_bv 64 (x / 4).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  replace (bv_unsigned (bv_and (Z_to_bv 64 2) (Z_to_bv 64 63))) with 2 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (0 <= x / 4 < 2 ^ 64) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small (x / 4)) by lia. reflexivity.
Qed.

Lemma lp_arith : forall N n, n = N / 4 -> 4 <= N ->
  1 <= n /\ 4 * n <= N < 4 * n + 4 /\ N / 8 = n / 2 /\ (4 * n) / 8 = n / 2 /\ 0 <= n / 2 /\ 8 * (n / 2) <= 4 * n
  /\ (Z.odd n = true -> 4 * (n - 1) = 8 * (n / 2) /\ 4 <= N mod 8 < 8 /\ (4 * n) mod 8 = 4 /\ N = 8 * (N / 8) + N mod 8)
  /\ (Z.odd n = false -> 4 * n = 8 * (n / 2)).
Proof.
  intros N n HN H4. subst n. rewrite Zodd_mod.
  destruct (Z.eqb_spec ((N / 4) mod 2) 1) as [E|E]; Z.div_mod_to_equations; repeat split; try lia; intros; try discriminate; lia.
Qed.

Lemma mod8_16 : forall D q, D mod 16 = 0 -> (D + 8 * q) mod 8 = 0.
Proof. intros D q HD. Z.div_mod_to_equations. lia. Qed.

Lemma nsh_room : forall P k C, P mod 16 = 0 -> k mod 4 = 0 -> 0 <= k -> P + k <= C -> C mod 16 = 0 -> P + 8 * nsh k <= C.
Proof. intros P k C HP Hk Hk0 HC HC16. unfold nsh. Z.div_mod_to_equations. lia. Qed.

Section TopL1.
  Context {HCEIL : HeapCeil}.

#[local] Definition HTLbATopL1_0 : list (reg * expr) := [(21%bv, EVar 32); (12%bv, EAlu ALU_ADD (EVar 32) (ELit 1)); (10%bv, EVar 33); (14%bv, EVar 33); (13%bv, EVar 34); (26%bv, ELit 2147450880)].
  Lemma lp_last0 : forall R F fc M ro (c d k z0 z1 z2 z3 : Z),
    getr R 21 = Z_to_bv 64 c -> getr R 12 = Z_to_bv 64 (c + 1) -> getr R 10 = Z_to_bv 64 d -> getr R 14 = Z_to_bv 64 d ->
    getr R 13 = Z_to_bv 64 k -> getr R 26 = Z_to_bv 64 0x7fff8000 ->
    k = 1 -> 0 <= c -> c + 4 <= 2 ^ 47 -> 0 <= d -> d + 4 <= 2 ^ 47 ->
    gz M c 4 -> sh0 M d -> wr_at asegs M d 4 ->
    rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z0] -> rdn asegs M (Z_to_bv 64 (c + 1)) 1 = Some [Z_to_bv 8 z1] ->
    rdn asegs M (Z_to_bv 64 (c + 2)) 1 = Some [Z_to_bv 8 z2] -> rdn asegs M (Z_to_bv 64 (c + 3)) 1 = Some [Z_to_bv 8 z3] ->
    0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M' ro)
      /\ getr R' 21 = Z_to_bv 64 (c + 4) /\ getr R' 12 = Z_to_bv 64 (c + 5) /\ getr R' 10 = Z_to_bv 64 (d + 4)
      /\ getr R' 14 = Z_to_bv 64 (d + 4) /\ getr R' 13 = Z_to_bv 64 (k - 1) /\ getr R' 26 = Z_to_bv 64 0x7fff8000
      /\ kept_in KSL R R' /\ munch [(d, d + 4)] M M' /\ wmono asegs M M'.
  Proof.
    intros until z3. intros H21 H12 H10 H14 H13 H26 Hk Hc0 Hc1 Hd0 Hd1 GZ SD WD B0 B1 B2 B3 Z0 Z1 Z2 Z3.
    pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 d; Z_to_bv 64 k; Z_to_bv 64 z0; Z_to_bv 64 z1; Z_to_bv 64 z2; Z_to_bv 64 z3]).
    assert (HR : regs_ok E (srs sr_id HTLbATopL1_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
        rewrite ?w_add by lia; [exact H21 | exact H12 | exact H10 | exact H14 | exact H13 | exact H26]. }
    assert (HK : know_ok asegs E M
       (kn_fix 10 [LP_HEAD; LP_EXIT] (SCR [] [] []) LP_HEAD
          (srs sr_id HTLbATopL1_0)
          [ KWord (SA (EVar 32) 0) 1 (EVar 35); KWord (SA (EVar 32) 1) 1 (EVar 36); KWord (SA (EVar 32) 2) 1 (EVar 37);
            KWord (SA (EVar 32) 3) 1 (EVar 38); KWr (SA (EVar 33) 0) (ELit 4);
            KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 34) 1 1;
            KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255 ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [eapply (kbyte E M _ _ c 0 z0); [evs; reflexivity | evs; reflexivity | lia | lia | lia | rewrite Z.add_0_r; exact B0 | exact Z0]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 1 z1); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B1 | exact Z1]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 2 z2); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B2 | exact Z2]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 3 z3); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B3 | exact Z3]|].
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WD | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
          | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 7 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 80%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    rreg HR' 21%bv G21. rreg HR' 12%bv G12. rreg HR' 10%bv G10. rreg HR' 14%bv G14. rreg HR' 13%bv G13. rreg HR' 26%bv G26.
    split; [rewrite G21, ?w_add by lia; reflexivity|]. split; [rewrite G12, ?w_add by lia; reflexivity|].
    split; [rewrite G10, ?w_add by lia; reflexivity|]. split; [rewrite G14, ?w_add by lia; reflexivity|].
    split; [rewrite G13; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G26|].
    split; [intros r Hr; eapply (syms_id_sound R _ _ R' KSL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
    split; [| subst M1; apply wmono_mem_denot].
    subst M1. clear - Hlf Hd0 Hd1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
    apply Forall_nil.
  Qed.
  Lemma lp_mid : forall R F fc M ro (c d k z0 z1 z2 z3 : Z),
    getr R 21 = Z_to_bv 64 c -> getr R 12 = Z_to_bv 64 (c + 1) -> getr R 10 = Z_to_bv 64 d -> getr R 14 = Z_to_bv 64 d ->
    getr R 13 = Z_to_bv 64 k -> getr R 26 = Z_to_bv 64 0x7fff8000 ->
    2 <= k < 2 ^ 45 -> 0 <= c -> c + 4 <= 2 ^ 47 -> 0 <= d -> d + 4 <= 2 ^ 47 ->
    gz M c 4 -> sh0 M d -> wr_at asegs M d 4 ->
    rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z0] -> rdn asegs M (Z_to_bv 64 (c + 1)) 1 = Some [Z_to_bv 8 z1] ->
    rdn asegs M (Z_to_bv 64 (c + 2)) 1 = Some [Z_to_bv 8 z2] -> rdn asegs M (Z_to_bv 64 (c + 3)) 1 = Some [Z_to_bv 8 z3] ->
    0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_HEAD) fc None M' ro)
      /\ getr R' 21 = Z_to_bv 64 (c + 4) /\ getr R' 12 = Z_to_bv 64 (c + 5) /\ getr R' 10 = Z_to_bv 64 (d + 4)
      /\ getr R' 14 = Z_to_bv 64 (d + 4) /\ getr R' 13 = Z_to_bv 64 (k - 1) /\ getr R' 26 = Z_to_bv 64 0x7fff8000
      /\ kept_in KSL R R' /\ munch [(d, d + 4)] M M' /\ wmono asegs M M'.
  Proof.
    intros until z3. intros H21 H12 H10 H14 H13 H26 Hk Hc0 Hc1 Hd0 Hd1 GZ SD WD B0 B1 B2 B3 Z0 Z1 Z2 Z3.
    pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 d; Z_to_bv 64 k; Z_to_bv 64 z0; Z_to_bv 64 z1; Z_to_bv 64 z2; Z_to_bv 64 z3]).
    assert (HR : regs_ok E (srs sr_id HTLbATopL1_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
        rewrite ?w_add by lia; [exact H21 | exact H12 | exact H10 | exact H14 | exact H13 | exact H26]. }
    assert (HK : know_ok asegs E M
       (kn_fix 10 [LP_HEAD; LP_EXIT] (SCR [] [] []) LP_HEAD
          (srs sr_id HTLbATopL1_0)
          [ KWord (SA (EVar 32) 0) 1 (EVar 35); KWord (SA (EVar 32) 1) 1 (EVar 36); KWord (SA (EVar 32) 2) 1 (EVar 37);
            KWord (SA (EVar 32) 3) 1 (EVar 38); KWr (SA (EVar 33) 0) (ELit 4);
            KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 34) 2 (2 ^ 45);
            KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255 ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [eapply (kbyte E M _ _ c 0 z0); [evs; reflexivity | evs; reflexivity | lia | lia | lia | rewrite Z.add_0_r; exact B0 | exact Z0]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 1 z1); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B1 | exact Z1]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 2 z2); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B2 | exact Z2]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 3 z3); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B3 | exact Z3]|].
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WD | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
          | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 7 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 80%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    rreg HR' 21%bv G21. rreg HR' 12%bv G12. rreg HR' 10%bv G10. rreg HR' 14%bv G14. rreg HR' 13%bv G13. rreg HR' 26%bv G26.
    split; [rewrite G21, ?w_add by lia; reflexivity|]. split; [rewrite G12, ?w_add by lia; reflexivity|].
    split; [rewrite G10, ?w_add by lia; reflexivity|]. split; [rewrite G14, ?w_add by lia; reflexivity|].
    split; [rewrite G13; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G26|].
    split; [intros r Hr; eapply (syms_id_sound R _ _ R' KSL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
    split; [| subst M1; apply wmono_mem_denot].
    subst M1. clear - Hlf Hd0 Hd1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
    apply Forall_nil.
  Qed.
  Lemma lp_last3 : forall R F fc M ro (c d k v z0 z1 z2 z3 : Z),
    getr R 21 = Z_to_bv 64 c -> getr R 12 = Z_to_bv 64 (c + 1) -> getr R 10 = Z_to_bv 64 d -> getr R 14 = Z_to_bv 64 d ->
    getr R 13 = Z_to_bv 64 k -> getr R 26 = Z_to_bv 64 0x7fff8000 ->
    k = 1 -> 0 <= c -> c + 4 <= 2 ^ 47 -> 0 <= d -> d + 4 <= 2 ^ 47 ->
    c mod 8 = 0 -> d mod 8 = 0 -> 4 <= v < 8 ->
    shk M c v -> shk M (c + 1) v -> shk M (c + 2) v -> shk M (c + 3) v -> shk M d 4 -> wr_at asegs M d 4 ->
    rdn asegs M (Z_to_bv 64 c) 1 = Some [Z_to_bv 8 z0] -> rdn asegs M (Z_to_bv 64 (c + 1)) 1 = Some [Z_to_bv 8 z1] ->
    rdn asegs M (Z_to_bv 64 (c + 2)) 1 = Some [Z_to_bv 8 z2] -> rdn asegs M (Z_to_bv 64 (c + 3)) 1 = Some [Z_to_bv 8 z3] ->
    0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M' ro)
      /\ getr R' 21 = Z_to_bv 64 (c + 4) /\ getr R' 12 = Z_to_bv 64 (c + 5) /\ getr R' 10 = Z_to_bv 64 (d + 4)
      /\ getr R' 14 = Z_to_bv 64 (d + 4) /\ getr R' 13 = Z_to_bv 64 (k - 1) /\ getr R' 26 = Z_to_bv 64 0x7fff8000
      /\ kept_in KSL R R' /\ munch [(d, d + 4)] M M' /\ wmono asegs M M'.
  Proof.
    intros until z3. intros H21 H12 H10 H14 H13 H26 Hk Hc0 Hc1 Hd0 Hd1 C8 D8 Hv S0 S1 S2 S3 SD WD B0 B1 B2 B3 Z0 Z1 Z2 Z3.
    pose (E := Eseed R [Z_to_bv 64 c; Z_to_bv 64 d; Z_to_bv 64 k; Z_to_bv 64 z0; Z_to_bv 64 z1; Z_to_bv 64 z2; Z_to_bv 64 z3; Z_to_bv 64 v]).
    assert (HR : regs_ok E (srs sr_id HTLbATopL1_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
        rewrite ?w_add by lia; [exact H21 | exact H12 | exact H10 | exact H14 | exact H13 | exact H26]. }
    assert (HK : know_ok asegs E M
          [ KWord (SA (EVar 32) 0) 1 (EVar 35); KWord (SA (EVar 32) 1) 1 (EVar 36); KWord (SA (EVar 32) 2) 1 (EVar 37);
            KWord (SA (EVar 32) 3) 1 (EVar 38); KWr (SA (EVar 33) 0) (ELit 4);
            KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 34) 1 1;
            KRange (EVar 35) 0 255; KRange (EVar 36) 0 255; KRange (EVar 37) 0 255; KRange (EVar 38) 0 255;
            KRange (EVar 39) 4 7; KAlign (EVar 32) 8; KAlign (EVar 33) 8;
            KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (EVar 39);
            KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 1)) (ELit 3)) SHBASE) 1 (EVar 39);
            KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 2)) (ELit 3)) SHBASE) 1 (EVar 39);
            KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 3)) (ELit 3)) SHBASE) 1 (EVar 39);
            KWord (SA (EAlu ALU_SRL (EVar 33) (ELit 3)) SHBASE) 1 (ELit 4) ]).
    { unfold know_ok.
      apply Forall_cons; [eapply (kbyte E M _ _ c 0 z0); [evs; reflexivity | evs; reflexivity | lia | lia | lia | rewrite Z.add_0_r; exact B0 | exact Z0]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 1 z1); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B1 | exact Z1]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 2 z2); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B2 | exact Z2]|].
      apply Forall_cons; [eapply (kbyte E M _ _ c 3 z3); [evs; reflexivity | evs; reflexivity | lia | lia | lia | exact B3 | exact Z3]|].
      apply Forall_cons.
      { eapply kwr_of_wr_at; [exact WD | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
          | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 8 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact C8]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact D8]|].
      apply Forall_cons; [eapply (kshadow E M _ c v); [evs; reflexivity | lia | lia | evs; reflexivity | exact S0]|].
      apply Forall_cons; [eapply (kshadow E M _ (c + 1) v); [evs; rewrite w_add by lia; reflexivity | lia | lia | evs; reflexivity | exact S1]|].
      apply Forall_cons; [eapply (kshadow E M _ (c + 2) v); [evs; rewrite w_add by lia; reflexivity | lia | lia | evs; reflexivity | exact S2]|].
      apply Forall_cons; [eapply (kshadow E M _ (c + 3) v); [evs; rewrite w_add by lia; reflexivity | lia | lia | evs; reflexivity | exact S3]|].
      apply Forall_cons; [eapply (kshadow E M _ d 4); [evs; reflexivity | lia | lia | reflexivity | exact SD]|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R LP_HEAD M ro HR HK 80%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    rreg HR' 21%bv G21. rreg HR' 12%bv G12. rreg HR' 10%bv G10. rreg HR' 14%bv G14. rreg HR' 13%bv G13. rreg HR' 26%bv G26.
    split; [rewrite G21, ?w_add by lia; reflexivity|]. split; [rewrite G12, ?w_add by lia; reflexivity|].
    split; [rewrite G10, ?w_add by lia; reflexivity|]. split; [rewrite G14, ?w_add by lia; reflexivity|].
    split; [rewrite G13; first [rewrite w_addm by lia; f_equal; lia | f_equal; lia]|]. split; [exact G26|].
    split; [intros r Hr; eapply (syms_id_sound R _ _ R' KSL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|].
    split; [| subst M1; apply wmono_mem_denot].
    subst M1. clear - Hlf Hd0 Hd1. apply munch_mem_denot; [exact Hlf|].
    repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
    apply Forall_nil.
  Qed.

  Lemma rdn1_munch : forall W M M' x, munch W M M' -> outside W x -> 0 <= x < 2 ^ 64 ->
    rdn asegs M' (Z_to_bv 64 x) 1 = rdn asegs M (Z_to_bv 64 x) 1.
  Proof.
    intros W M M' x MU OUT Hx. apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
    intros y Hy. rewrite u64_of_Z in Hy by lia. apply MU. replace (bv_unsigned y) with x by lia. exact OUT.
  Qed.
  Lemma shk_munch : forall W M M' x k, munch W M M' -> outside W (x / 8 + SHBASE) -> 0 <= x < 2 ^ 47 -> shk M x k -> shk M' x k.
  Proof.
    intros W M M' x k MU OUT Hx S. unfold shk in *. rewrite <- S. apply (rdn1_munch W); [exact MU | exact OUT |].
    assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). unfold SHBASE. lia.
  Qed.

  Lemma lp_loop : forall (K : nat) R F fc M ro (c d : Z) (odd : bool) (v : Z),
    getr R 21 = Z_to_bv 64 c -> getr R 12 = Z_to_bv 64 (c + 1) -> getr R 10 = Z_to_bv 64 d -> getr R 14 = Z_to_bv 64 d ->
    getr R 13 = Z_to_bv 64 (Z.of_nat (S K)) -> getr R 26 = Z_to_bv 64 0x7fff8000 ->
    Z.of_nat (S K) < 2 ^ 45 -> 0 <= c -> c + 4 * Z.of_nat (S K) <= 2 ^ 47 -> 0 <= d -> d + 4 * Z.of_nat (S K) <= 2 ^ 47 ->
    (c + 4 * Z.of_nat (S K) <= d \/ d + 4 * Z.of_nat (S K) <= c) ->
    (d + 4 * Z.of_nat (S K) <= 0x7fff8000 \/ 0x10007fff8000 <= d) ->
    wr_at asegs M d (4 * Z.of_nat (S K)) ->
    (forall j, 0 <= j < 4 * Z.of_nat (S K) -> exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z]) ->
    (forall j, 0 <= j < 4 * Z.of_nat K -> sh0 M (c + j)) -> (forall j, 0 <= j < Z.of_nat K -> sh0 M (d + 4 * j)) ->
    (if odd then (c + 4 * Z.of_nat K) mod 8 = 0 /\ (d + 4 * Z.of_nat K) mod 8 = 0 /\ 4 <= v < 8
                 /\ (forall j, 0 <= j < 4 -> shk M (c + 4 * Z.of_nat K + j) v) /\ shk M (d + 4 * Z.of_nat K) 4
     else (forall j, 0 <= j < 4 -> sh0 M (c + 4 * Z.of_nat K + j)) /\ sh0 M (d + 4 * Z.of_nat K)) ->
    exists R' M', CatSim.msteps asegs (MS R F (Z_to_bv 64 LP_HEAD) fc None M ro) (MS R' F (Z_to_bv 64 LP_EXIT) fc None M' ro)
      /\ kept_in KSL R R' /\ getr R' 26 = Z_to_bv 64 0x7fff8000 /\ munch [(d, d + 4 * Z.of_nat (S K))] M M' /\ wmono asegs M M'.
  Proof.
    induction K as [|K IH]; intros R F fc M ro c d odd v H21 H12 H10 H14 H13 H26 HK Hc0 Hc1 Hd0 Hd1 DJ BAND WD BY SC SD LAST.
    - change (Z.of_nat 0) with 0 in *. change (Z.of_nat 1) with 1 in *. rewrite !Z.mul_0_r, !Z.add_0_r in LAST.
      destruct (BY 0 ltac:(lia)) as (z0 & Z0 & B0). destruct (BY 1 ltac:(lia)) as (z1 & Z1 & B1).
      destruct (BY 2 ltac:(lia)) as (z2 & Z2 & B2). destruct (BY 3 ltac:(lia)) as (z3 & Z3 & B3).
      rewrite Z.add_0_r in B0.
      destruct odd.
      + destruct LAST as (C8 & D8 & Hv & SS & SDD).
        pose proof (SS 0 ltac:(lia)) as SS0. rewrite Z.add_0_r in SS0.
        destruct (lp_last3 R F fc M ro c d 1 v z0 z1 z2 z3 H21 H12 H10 H14 H13 H26 eq_refl Hc0 ltac:(lia) Hd0 ltac:(lia)
                    C8 D8 Hv SS0 (SS 1 ltac:(lia)) (SS 2 ltac:(lia)) (SS 3 ltac:(lia)) SDD WD B0 B1 B2 B3 Z0 Z1 Z2 Z3)
          as (R' & M' & RUN & _ & _ & _ & _ & _ & G26 & GK & MU & WM).
        exists R', M'. split; [exact RUN|]. split; [exact GK|]. split; [exact G26|]. split; [exact MU | exact WM].
      + destruct LAST as (SS & SDD).
        assert (GZ : gz M c 4) by (intros i Hi; exact (SS i Hi)).
        destruct (lp_last0 R F fc M ro c d 1 z0 z1 z2 z3 H21 H12 H10 H14 H13 H26 eq_refl Hc0 ltac:(lia) Hd0 ltac:(lia)
                    GZ SDD WD B0 B1 B2 B3 Z0 Z1 Z2 Z3)
          as (R' & M' & RUN & _ & _ & _ & _ & _ & G26 & GK & MU & WM).
        exists R', M'. split; [exact RUN|]. split; [exact GK|]. split; [exact G26|]. split; [exact MU | exact WM].
    - destruct (BY 0 ltac:(lia)) as (z0 & Z0 & B0). destruct (BY 1 ltac:(lia)) as (z1 & Z1 & B1).
      destruct (BY 2 ltac:(lia)) as (z2 & Z2 & B2). destruct (BY 3 ltac:(lia)) as (z3 & Z3 & B3).
      rewrite Z.add_0_r in B0.
      assert (GZ : gz M c 4) by (intros i Hi; apply SC; lia).
      assert (SD0 : sh0 M d) by (replace d with (d + 4 * 0) by lia; apply SD; lia).
      assert (WD4 : wr_at asegs M d 4) by (destruct WD as (W0 & W1 & W); split; [lia|]; split; [lia|]; intros i Hi; apply W; lia).
      destruct (lp_mid R F fc M ro c d (Z.of_nat (S (S K))) z0 z1 z2 z3 H21 H12 H10 H14 H13 H26 ltac:(lia) Hc0 ltac:(lia) Hd0 ltac:(lia)
                  GZ SD0 WD4 B0 B1 B2 B3 Z0 Z1 Z2 Z3)
        as (R1 & M1 & RUN1 & G21 & G12 & G10 & G14 & G13 & G26 & GK1 & MU1 & WM1).

      assert (OUTs : forall x, 0 <= x < 2 ^ 47 -> outside [(d, d + 4)] (x / 8 + SHBASE)).
      { intros x Hx. cbn. split; [| exact I]. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold SHBASE. lia. }
      destruct (IH R1 F fc M1 ro (c + 4) (d + 4) odd v G21 ltac:(rewrite G12; f_equal; lia) G10 G14
                  ltac:(rewrite G13; f_equal; lia) G26 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
        as (R' & M' & RUN2 & GK2 & G26' & MU2 & WM2).
      + destruct WD as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. apply WM1.
        replace (d + 4 + i) with (d + (4 + i)) by lia. apply W. lia.
      + intros j Hj. destruct (BY (4 + j) ltac:(lia)) as (z & Hz & Bz). exists z. split; [exact Hz|].
        rewrite (rdn1_munch _ M M1 (c + 4 + j) MU1 ltac:(cbn; split; [lia | exact I]) ltac:(lia)).
        replace (c + 4 + j) with (c + (4 + j)) by lia. exact Bz.
      + intros j Hj. eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia |]. replace (c + 4 + j) with (c + (4 + j)) by lia. apply SC. lia.
      + intros j Hj. eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia |].
        replace (d + 4 + 4 * j) with (d + 4 * (j + 1)) by lia. apply SD. lia.
      + replace (c + 4 + 4 * Z.of_nat K) with (c + 4 * Z.of_nat (S K)) by lia.
        replace (d + 4 + 4 * Z.of_nat K) with (d + 4 * Z.of_nat (S K)) by lia.
        destruct odd.
        * destruct LAST as (C8 & D8 & Hv & SS & SDD). split; [exact C8|]. split; [exact D8|]. split; [exact Hv|]. split.
          -- intros j Hj. eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia | apply SS; exact Hj].
          -- eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia | exact SDD].
        * destruct LAST as (SS & SDD). split.
          -- intros j Hj. eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia | apply SS; exact Hj].
          -- eapply (shk_munch _ M M1); [exact MU1 | apply OUTs; lia | lia | exact SDD].
      + exists R', M'. split; [exact (CatSim.msteps_trans _ _ _ _ RUN1 RUN2)|].
        split; [exact (kept_in_trans _ _ _ _ GK1 GK2)|]. split; [exact G26'|].
        split; [| exact (wmono_trans asegs _ _ _ WM1 WM2)].
        eapply munch_weaken; [| exact (munch_app _ _ _ _ _ MU1 MU2)].
        intros x Hx. cbn in Hx |- *. lia.
  Qed.

  Lemma hLP1 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N V A P : Z),
    4 <= N < 2 ^ 26 -> 0 <= D < 2 ^ 47 -> 0 <= V -> V + 24 <= 2 ^ 47 -> 0 <= P < 2 ^ 47 ->
    rw_cells asegs m V [C8 (wz P)] ->
    evt asegs (fun ms' => exists x10' x11' x13' x14' x12',
        ms' = MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10' x11' x12' x13' x14' x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 (N - 4)) (Z_to_bv 64 V)
                      (Z_to_bv 64 A) (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 LP_HEAD) fc None m (seg_rom asegs)
        /\ x10' = Z_to_bv 64 P /\ x14' = Z_to_bv 64 P /\ x13' = Z_to_bv 64 (N / 4) /\ x12' = Z_to_bv 64 (D + 1))
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 V)
               (Z_to_bv 64 A) (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8e28) fc None m (seg_rom asegs)).
  Proof.
    intros until P. intros HN HD HV0 HV1 HP CV.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 D) (Z_to_bv 64 N) (Z_to_bv 64 V)
               (Z_to_bv 64 A) (Z_to_bv 64 ff) (Z_to_bv 64 0x7fff8000) x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 D; Z_to_bv 64 N; Z_to_bv 64 V; Z_to_bv 64 P]).
    assert (HR : regs_ok E (srs sr_id [(21%bv, EVar 32); (22%bv, EVar 33); (23%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 34) 0) 8 (EVar 35); KRange (EVar 32) 0 (2 ^ 47); KRange (EVar 33) 4 (2 ^ 26);
                                     KRange (EVar 34) 0 (2 ^ 47); KRange (EVar 35) 0 (2 ^ 47) ]).
    { unfold know_ok. apply Forall_cons. { kword_cell CV 0%nat (C8 (wz P)). }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]). apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8e28 m (seg_rom asegs) HR HK 30%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 10%bv L10. rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 14%bv L14. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    assert (L22' : getr R' 22 = Z_to_bv 64 (N - 4)) by (rewrite L22, w_addm by lia; f_equal).
    assert (L12' : getr R' 12 = Z_to_bv 64 (D + 1)) by (rewrite L12, w_add by lia; reflexivity).
    assert (L13' : getr R' 13 = Z_to_bv 64 (N / 4)).
    { rewrite L13, w_addm by lia. rewrite srl2_val by lia.
      assert (Q : (N - 4) / 4 + 1 = N / 4).
      { replace N with ((N - 4) + 1 * 4) at 2 by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (QR : 0 <= (N - 4) / 4 < 2 ^ 62) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      replace (N + -4) with (N - 4) by lia. rewrite <- Q. set (q := (N - 4) / 4) in *. clearbody q. rewrite w_add by lia. reflexivity. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L21, L22', L23. cbn [mem_denot].
    apply evt_done. do 5 eexists. split; [subst R; reflexivity|].
    split; [exact L10|]. split; [exact L14|]. split; [exact L13' | exact L12'].
  Qed.

  Lemma hLP0 : forall (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N : Z),
    0 <= N < 4 ->
    evt asegs (fun ms' =>
        ms' = MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 4) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) x21 (Z_to_bv 64 N) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 LP_EXIT) fc None m (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) x21 (Z_to_bv 64 N) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8e28) fc None m (seg_rom asegs)).
  Proof.
    intros until N. intros HN.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 (sh ff + 4)) x21 (Z_to_bv 64 N) x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 N]).
    assert (HR : regs_ok E (srs sr_id [(22%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m [ KRange (EVar 32) 0 3 ]).
    { unfold know_ok. apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xe8e28 m (seg_rom asegs) HR HK 10%nat [LP_HEAD; LP_EXIT] (SCR [] [] []) 40%N.
    { split_scs. }
    clear HK.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 10%bv L10. rreg HR' 22%bv L22.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L10, L22. cbn [mem_denot]. apply evt_done. reflexivity.
  Qed.
End TopL1.
