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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGb1 LbB_RGb2 LbB_RG2 LbB_Ctx LbB_TopH1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TOP_F8_RA : Z := 0xe8998.
Definition TOP_00_RA : Z := 0xe8a24.
Definition TOP_RET6 : Z := 0xe8c54.
Definition TOP_RG_RA : Z := 0xe8a34.
Definition TOP_GTE_RA : Z := 0xe8a3c.
Definition TOP_CTX_RA : Z := 0xe8a40.

Lemma sh_q : forall ff, 0 <= ff < 2 ^ 47 -> ff mod 64 = 0 ->
  mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000).
Proof.
  intros ff H1 H2. rewrite w_mul by (Z.div_mod_to_equations; lia). f_equal.
  unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
Qed.

Section TopH2.
  Context {HCEIL : HeapCeil}.

  Definition h2a_post (gp tp s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff N lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 313) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                    s7 s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 ASET_SHADOW_F8) fc None m1 (seg_rom asegs)
      /\ munch [(S1 + 104, S1 + 112); (ff, ff + 24); (sh ff, sh ff + 4)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo SP.

  Lemma h2a : forall (gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s6 s7 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N lo : Z),
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 224 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m ff 24 -> wr_at asegs m (sh ff) 4 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h2a_post gp tp s7 s8 s9 s10 F fc SP S1 ff N lo m)
      (MS (mkR (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
               x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 (Z_to_bv 64 N)
               x28 x29 x30 x31) F (Z_to_bv 64 TOP_SM_RET) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s6 s7 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff N lo
      S32 S1L S1H SPH LO F64 FLO FHI WF WS ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - SHBASE)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHQ : 8 * (ff / 64) = sh ff - 0x7fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 N; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 64) (EVar 32)); (2%bv, EVar 33); (9%bv, EVar 33); (8%bv, EVar 36); (21%bv, ELit 2147450880); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity. rewrite Q. reflexivity. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - SHBASE)
      by (evs; rewrite QS, u64_of_Z by (unfold SHBASE in *; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EVar 33) 0) (ELit 224); KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 24); KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) 2147450880) (ELit 4); KRange (EVar 33) 35184372088832 140737488355328; KAlign (EVar 33) 32; KRange (EVar 32) (0x6e6000 / 64) 2199023255552]).
    { unfold know_ok.
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. split; [lia | rewrite EP; exact S32]. }
      apply Forall_cons. { cbn [kentry_ok]. evs.
        rewrite u64_of_Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). Z.div_mod_to_equations. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_SM_RET m (seg_rom asegs) HR HK 120%nat [770580] (SCR [] [] []) 40%N.
    { split_scs. }
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
    rreg HR' 18%bv L18.
    rreg HR' 19%bv L19.
    rreg HR' 20%bv L20.
    rreg HR' 21%bv L21.
    rreg HR' 22%bv L22.
    rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_F8_RA)) by (rewrite L1; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by (rewrite L2; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by (rewrite L8; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by (rewrite L9; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L10' : getr R' 10 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L10; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L11' : getr R' 11 = (Z_to_bv 64 313)) by (rewrite L11; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L18' : getr R' 18 = (Z_to_bv 64 ff)) by (rewrite L18; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L19; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by (rewrite L20; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L21' : getr R' 21 = (Z_to_bv 64 (sh ff))) by (rewrite L21; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L22' : getr R' 22 = (Z_to_bv 64 0x7fff8000)) by (rewrite L22; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L27' : getr R' 27 = (Z_to_bv 64 N)) by (rewrite L27; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (MU1 : munch [(S1 + 104, S1 + 112); (ff, ff + 24); (sh ff, sh ff + 4)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?Q, ?QS; rewrite ?u64_of_Z by (unfold SHBASE in *; lia);
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L18', L19', L20', L21', L22', L27'.
    apply evt_done.
    do 14 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition h3a_post (gp tp s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff N lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                    (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 313) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                    (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 ASET_SHADOW_00) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 317, sh ff + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.

  Lemma h3a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N lo : Z),
    1 <= N < 2 ^ 26 -> 0 <= S1 <= 2 ^ 47 -> 0 <= SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m (sh ff + 317) 27 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h3a_post gp tp s8 s9 s10 F fc SP S1 ff N lo m)
      (MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 TOP_F8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff N lo
      NR S1R SPR F64 FLO FHI WS ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - SHBASE)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHQ : 8 * (ff / 64) = sh ff - 0x7fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 N; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33); (8%bv, EVar 36); (18%bv, EMd M_MUL (ELit 64) (EVar 32)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450884)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (22%bv, ELit 2147450880); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor.
      all: cbn [fst snd]; try (intros X; discriminate X).
      all: subst R; evs.
      all: try reflexivity.
      all: rewrite ?Q, ?QS.
      all: rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia).
      all: first [reflexivity | refine (eq_trans (y := Z_to_bv 64 _) eq_refl _); f_equal; unfold SHBASE in *; lia]. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - SHBASE)
      by (evs; rewrite QS, u64_of_Z by (unfold SHBASE in *; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) 2147451197) (ELit 27); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 32) (0x6e6000 / 64) 2199023255552; KRange (EVar 35) 0 67108864]).
    { unfold know_ok. repeat (apply Forall_cons; [first
        [ eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]
        | cbn [kentry_ok]; rewrite EP; lia
        | cbn [kentry_ok]; evs; rewrite u64_of_Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
          Z.div_mod_to_equations; lia
        | cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia ] |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_F8_RA m (seg_rom asegs) HR HK 120%nat [770292; 953428] (SCR [false] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; evs; try change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite HLib.br_eq by lia; first [apply Z.eqb_neq | apply Z.eqb_eq]; lia. }
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
    rreg HR' 22%bv L22.
    rreg HR' 23%bv L23.
    rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_00_RA)) by (rewrite L1; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by (rewrite L2; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by (rewrite L8; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by (rewrite L9; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L10' : getr R' 10 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L10; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L11' : getr R' 11 = (Z_to_bv 64 313)) by (rewrite L11; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L18' : getr R' 18 = (Z_to_bv 64 ff)) by (rewrite L18; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L19; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by (rewrite L20; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L21' : getr R' 21 = (Z_to_bv 64 (sh ff))) by (rewrite L21; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L22' : getr R' 22 = (Z_to_bv 64 0x7fff8000)) by (rewrite L22; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L23' : getr R' 23 = (Z_to_bv 64 (ff + 32))) by (rewrite L23; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L27' : getr R' 27 = (Z_to_bv 64 N)) by (rewrite L27; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (MU1 : munch [(sh ff + 317, sh ff + 344)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?Q, ?QS; rewrite ?u64_of_Z by (unfold SHBASE in *; lia);
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L11', L18', L19', L20', L21', L22', L23', L27'.
    apply evt_done.
    do 14 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition h3z_post (gp tp s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR x1 (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                    s7 s8 s9 s10 (Z_to_bv 64 0) x28 x29 x30 x31) F (Z_to_bv 64 TOP_RET6) fc None m1 (seg_rom asegs)
      /\ munch [(sh ff + 317, sh ff + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.

  Lemma h3z : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff lo : Z),
    0 <= S1 <= 2 ^ 47 -> 0 <= SP <= 2 ^ 47 ->
    ff mod 64 = 0 -> 0x6e6000 <= ff -> ff + 4096 <= 2 ^ 47 ->
    wr_at asegs m (sh ff + 317) 27 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (h3z_post gp tp s7 s8 s9 s10 F fc SP S1 ff lo m)
      (MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 (Z_to_bv 64 0) x28 x29 x30 x31) F (Z_to_bv 64 TOP_F8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s7 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff lo
      S1R SPR F64 FLO FHI WS ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - SHBASE)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHQ : 8 * (ff / 64) = sh ff - 0x7fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 (Z_to_bv 64 0) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33); (8%bv, EVar 36); (18%bv, EMd M_MUL (ELit 64) (EVar 32)); (19%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450884)); (20%bv, EMd M_MUL (ELit 64) (EVar 32)); (21%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880)); (22%bv, ELit 2147450880); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor.
      all: cbn [fst snd]; try (intros X; discriminate X).
      all: subst R; evs.
      all: try reflexivity.
      all: rewrite ?Q, ?QS.
      all: rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia).
      all: first [reflexivity | refine (eq_trans (y := Z_to_bv 64 _) eq_refl _); f_equal; unfold SHBASE in *; lia]. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = sh ff - SHBASE)
      by (evs; rewrite QS, u64_of_Z by (unfold SHBASE in *; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) 2147451197) (ELit 27); KRange (EVar 33) 0 (2 ^ 47); KRange (EVar 32) (0x6e6000 / 64) 2199023255552; KRange (EVar 35) 0 67108864]).
    { unfold know_ok. repeat (apply Forall_cons; [first
        [ eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
          | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
          | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]
        | cbn [kentry_ok]; rewrite EP; lia
        | cbn [kentry_ok]; evs; rewrite u64_of_Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
          Z.div_mod_to_equations; lia
        | cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia ] |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_F8_RA m (seg_rom asegs) HR HK 120%nat [770292; 953428] (SCR [true] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; evs; try change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite HLib.br_eq by lia; first [apply Z.eqb_neq | apply Z.eqb_eq]; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
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
    rreg HR' 22%bv L22.
    rreg HR' 27%bv L27.
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by (rewrite L2; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L8' : getr R' 8 = (Z_to_bv 64 SP)) by (rewrite L8; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by (rewrite L9; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L18' : getr R' 18 = (Z_to_bv 64 ff)) by (rewrite L18; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L19' : getr R' 19 = (Z_to_bv 64 (sh ff + 4))) by (rewrite L19; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L20' : getr R' 20 = (Z_to_bv 64 ff)) by (rewrite L20; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L21' : getr R' 21 = (Z_to_bv 64 (sh ff))) by (rewrite L21; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L22' : getr R' 22 = (Z_to_bv 64 0x7fff8000)) by (rewrite L22; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L27' : getr R' 27 = (Z_to_bv 64 0)) by (rewrite L27; rewrite ?Q, ?QS; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (MU1 : munch [(sh ff + 317, sh ff + 344)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?Q, ?QS; rewrite ?u64_of_Z by (unfold SHBASE in *; lia);
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L2', L8', L9', L18', L19', L20', L21', L22', L27'.
    apply evt_done.
    do 17 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Lemma h4a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff D N : Z),
    0 <= ff < 2 ^ 47 -> 0 <= D < 2 ^ 64 -> 0 <= S1 -> S1 + 96 <= 2 ^ 64 -> rw_cells asegs m (S1 + 88) [C8 (Z_to_bv 64 D)] ->
    evt asegs (fun ms' => exists x13' x14' x15' x16' x17',
        ms' = MS (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 D) (Z_to_bv 64 N) x13' x14' x15' x16' x17'
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                      (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 RG_CTOR) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_00_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff D N
      FR DR S1L S1H RC.
    remember (mkR (Z_to_bv 64 TOP_00_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff; Z_to_bv 64 S1; Z_to_bv 64 D; Z_to_bv 64 N; Z_to_bv 64 SP]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (9%bv, EVar 33); (18%bv, EVar 32); (23%bv, EAlu ALU_ADD (EVar 32) (ELit 32)); (27%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor.
      all: cbn [fst snd]; try (intros X; discriminate X).
      all: subst R; evs.
      all: try reflexivity.
      all: rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia).
      all: first [reflexivity | refine (eq_trans (y := Z_to_bv 64 _) eq_refl _); f_equal; unfold SHBASE in *; lia]. }
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [KWord (SA (EVar 33) 88) 8 (EVar 34); KRange (EVar 33) 0 (2 ^ 64 - 96); KRange (EVar 32) 0 (2 ^ 47)]).
    { unfold know_ok.
      apply Forall_cons. { eapply kword_of_rw_cells with (k := 0%nat); [exact RC | reflexivity | reflexivity | lia
                                  | unfold estart; cbn [a_base a_off]; rewrite EP; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_00_RA m (seg_rom asegs) HR HK 60%nat [1050136] (SCR [] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; evs; try change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite HLib.br_eq by lia; first [apply Z.eqb_neq | apply Z.eqb_eq]; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 2%bv L2.
    rreg HR' 9%bv L9.
    rreg HR' 10%bv L10.
    rreg HR' 11%bv L11.
    rreg HR' 12%bv L12.
    rreg HR' 18%bv L18.
    rreg HR' 23%bv L23.
    rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_RG_RA)) by (rewrite L1; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L2' : getr R' 2 = (Z_to_bv 64 S1)) by (rewrite L2; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L9' : getr R' 9 = (Z_to_bv 64 S1)) by (rewrite L9; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 32))) by (rewrite L10; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L11' : getr R' 11 = (Z_to_bv 64 D)) by (rewrite L11; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L12' : getr R' 12 = (Z_to_bv 64 N)) by (rewrite L12; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L18' : getr R' 18 = (Z_to_bv 64 ff)) by (rewrite L18; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L23' : getr R' 23 = (Z_to_bv 64 (ff + 32))) by (rewrite L23; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L27' : getr R' 27 = (Z_to_bv 64 N)) by (rewrite L27; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L9', L10', L11', L12', L18', L23', L27'.
    apply evt_done.
    do 5 eexists. subst M1. reflexivity.
  Qed.

  Lemma h5a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N : Z),
    0 <= ff < 2 ^ 47 ->
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      (Z_to_bv 64 (ff + 32)) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                      (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 GTE_ENTRY) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_RG_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff N
      FR.
    remember (mkR (Z_to_bv 64 TOP_RG_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok asegs E m []) by (unfold know_ok; apply Forall_nil).
    xrun_at (PropExec.mkFP F fc) asegs R TOP_RG_RA m (seg_rom asegs) HR HK 60%nat [1051184] (SCR [] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; evs; try change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite HLib.br_eq by lia; first [apply Z.eqb_neq | apply Z.eqb_eq]; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    rreg HR' 10%bv L10.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_GTE_RA)) by (rewrite L1, ?HR0; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    assert (L10' : getr R' 10 = (Z_to_bv 64 (ff + 32))) by (rewrite L10, ?HR0; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L10'.
    apply evt_done.
    subst M1. reflexivity.
  Qed.

  Lemma h6a : forall (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff N : Z),
    evt asegs (fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 TOP_CTX_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1)
                      x10 x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000)
                      (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) F (Z_to_bv 64 CTX_CREATE) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff))
               (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31)
          F (Z_to_bv 64 TOP_GTE_RA) fc None m (seg_rom asegs)).
  Proof.
    intros gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s8 s9 s10 x28 x29 x30 x31 F fc m SP S1 ff N
      .
    remember (mkR (Z_to_bv 64 TOP_GTE_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (ff + 32)) s8 s9 s10 (Z_to_bv 64 N) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok asegs E m []) by (unfold know_ok; apply Forall_nil).
    xrun_at (PropExec.mkFP F fc) asegs R TOP_GTE_RA m (seg_rom asegs) HR HK 60%nat [958280] (SCR [] [] []) 40%N.
    { split_scs.
      all: cbn [sc_denot]; evs; try change (edenot E (ELit 0)) with (Z_to_bv 64 0);
        rewrite HLib.br_eq by lia; first [apply Z.eqb_neq | apply Z.eqb_eq]; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1.
    assert (L1' : getr R' 1 = (Z_to_bv 64 TOP_CTX_RA)) by (rewrite L1, ?HR0; rewrite ?w_add, ?w_addm by (unfold SHBASE in *; lia); first [reflexivity | f_equal; unfold SHBASE in *; lia]).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1'.
    apply evt_done.
    subst M1. reflexivity.
  Qed.
End TopH2.
