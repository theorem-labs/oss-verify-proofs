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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_DStat LbB_RGb2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition KTO : list reg := [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Ltac os_tail_fin :=
  lazymatch goal with
  | Hlf : log_flat ?E ?lg, Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok _ _ ?R',
    HR0 : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    MI : mem_inv asegs ?m, EF : bv_unsigned (edenot _ (EMd M_MUL (ELit 64) (EVar 32))) = ?ff,
    ES : bv_unsigned (edenot _ (EMd M_MUL (ELit 8) (EVar 32))) = _, EQ : bv_unsigned (edenot _ (EVar 33)) = ?fp,
    WP : wr_at asegs ?m ?fp 1 |- _ =>
      change mm with (mem_denot E m lg) in Hms;
      let M1 := fresh "M1" in set (M1 := mem_denot E m lg) in Hms;
      exists R', M1; split; [exact Hms|];
      let HF := fresh "HF" in assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR);
      let HF1 := fresh "HF1" in pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1;
      let HRe := fresh "HRe" in readback HR' HF1 HR0 HRe;
      let L1 := fresh "L1" in let L2 := fresh "L2" in let L8 := fresh "L8" in let L9 := fresh "L9" in
      let L10 := fresh "L10" in let L18 := fresh "L18" in let L19 := fresh "L19" in let L20 := fresh "L20" in
      let L21 := fresh "L21" in
      rreg HR' 1%bv L1; rreg HR' 2%bv L2; rreg HR' 8%bv L8; rreg HR' 9%bv L9; rreg HR' 10%bv L10;
      rreg HR' 18%bv L18; rreg HR' 19%bv L19; rreg HR' 20%bv L20; rreg HR' 21%bv L21;
      split; [rewrite HRe at 1; rewrite L1, L2, L8, L9, L10, L18, L19, L20, L21; reflexivity|];
      split;
      [ subst M1; apply munch_mem_denot; [exact Hlf|];
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                    first [rewrite EF | rewrite ES | rewrite EQ];
                                    cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]);
        apply Forall_nil |];
      split; [subst M1; apply wmono_mem_denot|];
      split; [exact (msteps_mem_inv asegs _ _ Hms MI)|];
      split; [intros lo' hi' SK; subst M1; apply stk_mem_denot; exact SK|];
      let FL := fresh "FL" in
      assert (FL : rw_cells asegs M1 fp [C1 (b8 0)])
        by (subst M1; eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
              | unfold estart; cbn [a_base a_off]; rewrite EQ; lia | exact WP | reflexivity | exact I | reflexivity]);
      let B := fresh "B" in
      destruct FL as [[_ (_ & _ & B)] _]; specialize (B 0%nat ltac:(cbn; lia)); rewrite Z.add_0_r in B; exact B
  end.

Section OS2.
  Context {HCEIL : HeapCeil}.

  Lemma os_b3f : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (gp tp s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff SP S1 d : Z),
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> 0 <= d < 2 ^ 64 -> 0 < d -> d mod 4 = 0 ->
    rw_cells asegs m (ff + 32) [C8 (Z_to_bv 64 d)] ->
    exists R',
      CatSim.msteps asegs
        (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 0)
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 OS_LO_RET) fc None m ro)
        (MS R' F (Z_to_bv 64 AT_IDESC_NAME) fc None m ro)
      /\ R' = mkR (Z_to_bv 64 OS_NM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 d)
                 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.
  Proof.
    intros until d. intros F64 FLO FHI Hd D0 D4 CD.
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 0)
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff + 32); Z_to_bv 64 d]).
    assert (HR : regs_ok E (srs sr_id [(19%bv, EVar 32); (10%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        reflexivity. }
    assert (HK : know_ok asegs E m [KWord (SA (EVar 32) 0) 8 (EVar 33); KRange (EVar 33) 1 (2 ^ 64 - 1); KAlign (EVar 33) 4]).
    { unfold know_ok. apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 32) _ 0%nat (C8 (Z_to_bv 64 d))); [exact CD | reflexivity | reflexivity | lia
        | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; split; [lia | exact D4]|].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R OS_LO_RET m ro HR HK 20%nat [AT_IDESC_NAME] (SCR [] [] []) 40%N.
    { split_scs; subst E; sc_dj. }
    cbn [mem_denot] in Hms.
    exists R'. split; [exact Hms|].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 19%bv L19.
    rewrite HRe, L1, L10, L11, L19. subst R. reflexivity.
  Qed.

  Lemma os_tail : forall (b : bool) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff fp SP S1 res : Z),
    (if b then x10 <> Z_to_bv 64 0 /\ res = 0x25000 else x10 = Z_to_bv 64 res) ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> (ff + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0x6e8000 <= fp -> fp + 1 <= ff -> (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp) ->
    2 ^ 45 <= SP - 64 -> SP <= 2 ^ 47 -> ff + 64 <= SP - 64 ->
    rw_cells asegs m (SP - 56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m (ff + 56) [C8 (Z_to_bv 64 fp)] ->
    wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 8 -> wr_at asegs m fp 1 -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 (if b then OS_LO_RET else OS_NM_RET)) fc None m ro)
        (MS R' F (Z_to_bv 64 OS_RET) fc None M' ro)
      /\ R' = mkR ra (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 res) (getr R' 11)
                 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
      /\ munch [(sh ff, sh ff + 8); (ff, ff + 8); (fp, fp + 1)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ mrd asegs M' (wa fp) = Some (b8 0).
  Proof.
    intros until res. intros HB F64 FLO FHI FB PLO PFF PB SPL SPH SFF CSF CFP WF WS WP MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 8 <= 0x10007fff8000).
    { unfold sh; rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    remember (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 fp; Z_to_bv 64 SP; x10; ra; s0; s1; s2; s3; s4; s5]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 35); (8%bv, EVar 34); (18%bv, EMd M_MUL (ELit 64) (EVar 32));
                                       (20%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880));
                                       (21%bv, EMd M_MUL (ELit 64) (EVar 32))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
      transitivity (Z_to_bv 64 (sh ff)); [reflexivity | f_equal; unfold SHBASE in QS; lia]. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
      by (evs; rewrite w_mul by (Z.div_mod_to_equations; lia); rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 34)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EQ : bv_unsigned (edenot E (EVar 33)) = fp) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 56) 8 (EVar 33);
         KWord (SA (EVar 34) (-56)) 8 (EVar 42); KWord (SA (EVar 34) (-48)) 8 (EVar 41); KWord (SA (EVar 34) (-40)) 8 (EVar 40);
         KWord (SA (EVar 34) (-32)) 8 (EVar 39); KWord (SA (EVar 34) (-24)) 8 (EVar 38); KWord (SA (EVar 34) (-16)) 8 (EVar 37);
         KWord (SA (EVar 34) (-8)) 8 (EVar 36);
         KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
         KWr (SA (EVar 33) 0) (ELit 1);
         KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 0x6e8000 (2 ^ 47);
         KDisj (SA (EVar 34) (-64)) (ELit 64) (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
         KDisj (SA (EVar 34) (-64)) (ELit 64) (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
         KDisj (SA (EVar 34) (-64)) (ELit 64) (SA (EVar 33) 0) (ELit 1);
         KDisj (SA (EMd M_MUL (ELit 64) (EVar 32)) 56) (ELit 8) (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 56) _ 0%nat (C8 (Z_to_bv 64 fp))); [exact CFP | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { kword_cell CSF 0%nat (C8 s5). }
      apply Forall_cons. { kword_cell CSF 8%nat (C8 s4). }
      apply Forall_cons. { kword_cell CSF 16%nat (C8 s3). }
      apply Forall_cons. { kword_cell CSF 24%nat (C8 s2). }
      apply Forall_cons. { kword_cell CSF 32%nat (C8 s1). }
      apply Forall_cons. { kword_cell CSF 40%nat (C8 s0). }
      apply Forall_cons. { kword_cell CSF 48%nat (C8 ra). }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
                                  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [a_base a_off]; rewrite EQ; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EQ; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EQ. lia. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?EF, ?ES, ?EP, ?EQ; evs;
                                rewrite ?u64_of_Z by lia; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    destruct b.
    -
      destruct HB as [HB1 HB2].
      xrun_at (PropExec.mkFP F fc) asegs R OS_LO_RET m ro HR HK 100%nat [OS_RET] (SCR [false] [] []) 44%N.
      { split_scs. cbn [sc_denot]. subst E. evs.
        destruct (Z.eq_dec (bv_unsigned x10) 0) as [Z0|NZ]; [exfalso; apply HB1; apply bv_eq; rewrite Z0; reflexivity|].
        replace x10 with (Z_to_bv 64 (bv_unsigned x10)) by (apply Z_to_bv_bv_unsigned).
        pose proof (bv_unsigned_in_range 64 x10) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
        rewrite br_eq by lia. apply Z.eqb_neq. exact NZ. }
      subst res. os_tail_fin.
    - xrun_at (PropExec.mkFP F fc) asegs R OS_NM_RET m ro HR HK 100%nat [OS_RET] (SCR [] [] []) 44%N.
      { first [apply Forall_nil | split_scs]. }
      subst x10. os_tail_fin.
  Qed.
End OS2.
