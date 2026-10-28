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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_RGb2 LbB_WoR1 LbB_WoR2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_StateStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition EX_F5_RA : Z := 0xf8ffc.
Definition EX_RET : Z := 0xf904c.

Section ExR7.
  Context {HCEIL : HeapCeil}.

  Lemma xe2 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (gp tp : word) (ra' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff fp SP S1 r : Z),
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 512 <= S1 ->
    0x6e8000 <= fp -> fp + 1 <= ff ->
    2 ^ 45 <= S1 -> S1 + 128 <= SP -> SP <= 2 ^ 47 ->
    rw_cells asegs m (SP - 104) [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra'] ->
    rw_cells asegs m (ff + 504) [C8 (Z_to_bv 64 fp)] ->
    wr_at asegs m fp 1 -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21
                 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31) F (Z_to_bv 64 EX_F5_RA) fc None m ro)
        (MS R' F (Z_to_bv 64 EX_RET) fc None M' ro)
      /\ R' = mkR ra' (Z_to_bv 64 SP) gp tp x5 x6 x7 s0' s1' (Z_to_bv 64 r) x11
                 x12 x13 x14 x15 x16 x17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' x28 x29 x30 x31
      /\ munch [(fp, fp + 1)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ mrd asegs M' (wa fp) = Some (b8 0).
  Proof.
    intros until r. intros F64 FLO FS1 PLO PFF S1L S1H SPH CSF CFP WP MI.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) x9 x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) x19 (Z_to_bv 64 r) x21
                 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 fp; Z_to_bv 64 SP; s11'; s10'; s9'; s8'; s7'; s6'; s5'; s4'; s3'; s2'; s1'; s0'; ra']).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 34); (18%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity. }
    assert (EF : bv_unsigned (edenot E (EVar 32)) = ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 34)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EQ : bv_unsigned (edenot E (EVar 33)) = fp) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 504) 8 (EVar 33);
         KWord (SA (EVar 34) (-104)) 8 (EVar 35); KWord (SA (EVar 34) (-96)) 8 (EVar 36); KWord (SA (EVar 34) (-88)) 8 (EVar 37);
         KWord (SA (EVar 34) (-80)) 8 (EVar 38); KWord (SA (EVar 34) (-72)) 8 (EVar 39); KWord (SA (EVar 34) (-64)) 8 (EVar 40);
         KWord (SA (EVar 34) (-56)) 8 (EVar 41); KWord (SA (EVar 34) (-48)) 8 (EVar 42); KWord (SA (EVar 34) (-40)) 8 (EVar 43);
         KWord (SA (EVar 34) (-32)) 8 (EVar 44); KWord (SA (EVar 34) (-24)) 8 (EVar 45); KWord (SA (EVar 34) (-16)) 8 (EVar 46);
         KWord (SA (EVar 34) (-8)) 8 (EVar 47);
         KWr (SA (EVar 33) 0) (ELit 1);
         KRange (EVar 32) (0x6e8000 + 0x9000) (2 ^ 47); KRange (EVar 34) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 0x6e8000 (2 ^ 47);
         KDisj (SA (EVar 34) (-104)) (ELit 104) (SA (EVar 33) 0) (ELit 1) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 504) _ 0%nat (C8 (Z_to_bv 64 fp))); [exact CFP | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { kword_cell CSF 0%nat (C8 s11'). }
      apply Forall_cons. { kword_cell CSF 8%nat (C8 s10'). }
      apply Forall_cons. { kword_cell CSF 16%nat (C8 s9'). }
      apply Forall_cons. { kword_cell CSF 24%nat (C8 s8'). }
      apply Forall_cons. { kword_cell CSF 32%nat (C8 s7'). }
      apply Forall_cons. { kword_cell CSF 40%nat (C8 s6'). }
      apply Forall_cons. { kword_cell CSF 48%nat (C8 s5'). }
      apply Forall_cons. { kword_cell CSF 56%nat (C8 s4'). }
      apply Forall_cons. { kword_cell CSF 64%nat (C8 s3'). }
      apply Forall_cons. { kword_cell CSF 72%nat (C8 s2'). }
      apply Forall_cons. { kword_cell CSF 80%nat (C8 s1'). }
      apply Forall_cons. { kword_cell CSF 88%nat (C8 s0'). }
      apply Forall_cons. { kword_cell CSF 96%nat (C8 ra'). }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [a_base a_off]; rewrite EQ; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EQ; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EF. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EQ. lia. }
      apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?EF, ?EP, ?EQ; evs;
                          rewrite ?u64_of_Z by lia; lia|].
      apply Forall_nil. }
    unfold EX_F5_RA.
    xrun_at (PropExec.mkFP F fc) asegs R 0xf8ffc m ro HR HK 60%nat [EX_RET] (SCR [] [] []) 44%N.
    { first [apply Forall_nil | split_scs].
      all: cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; rewrite ?EF, ?EP, ?EQ; evs; rewrite ?u64_of_Z by lia; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 10%bv L10.
    rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rreg HR' 24%bv L24. rreg HR' 25%bv L25. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = Z_to_bv 64 SP) by (rewrite L2; evs; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L10' : getr R' 10 = Z_to_bv 64 r) by (rewrite L10; first [reflexivity | rewrite HR0; reflexivity | evs; reflexivity]).
    split; [rewrite HRe at 1; rewrite L1, L2', L8, L9, L10', L18, L19, L20, L21, L22, L23, L24, L25, L26, L27; subst R; reflexivity|].
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; rewrite EQ;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|].
    split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [intros lo' hi' SK; subst M1; apply stk_mem_denot; exact SK|].
    assert (FL : rw_cells asegs M1 fp [C1 (b8 0)]).
    { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite EQ; lia | exact WP | reflexivity | exact I | reflexivity]. }
    destruct FL as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B.
  Qed.
End ExR7.
