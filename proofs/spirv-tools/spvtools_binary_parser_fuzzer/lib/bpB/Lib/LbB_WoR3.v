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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_FKit LbB_WoR1 LbB_WoR2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition WO_MS1_RA : Z := 0xeb2bc.
Definition WO_MS2_RA : Z := 0xeb2cc.
Definition WO_MS3_RA : Z := 0xeb2e4.
Definition WO_MS4_RA : Z := 0xeb2f8.
Definition WO_MS5_RA : Z := 0xeb318.
Definition WO_ON1_RA : Z := 0xeb324.

Ltac djd EF' ES' := cbn [e_addr e_width]; unfold estart; HLib.evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia.

Ltac wr3_seed R :=
  apply regs_ok_srs; [apply regs_ok_seed|];
  repeat (apply Forall_cons; [split; [cbn [fst]; intros X; discriminate X
                                     | cbn [fst snd]; subst R; evs; first [reflexivity | rewrite w_add by lia; reflexivity]] |]);
  apply Forall_nil.

Ltac wr3_kwr WR :=
  eapply kwr_of_wr_at;
  [ exact WR | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia
  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia ].

Ltac wr3_sc :=
  first [ apply Forall_nil
        | split_scs; cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia; lia ].

Ltac wr3_r HR' HR0 r L T :=
  let G := fresh "G" in
  rreg HR' r G;
  assert (L : T) by (rewrite G; first [ reflexivity | rewrite HR0; reflexivity
                                      | rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia] ]);
  clear G.

Ltac wr3_mem E m Hlf Hms M1 :=
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.

Ltac wr3_munch M1 Hlf :=
  subst M1; apply munch_mem_denot; [exact Hlf|];
  repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia;
                              cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]);
  apply Forall_nil.

Ltac wr3_dj := cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?u64_of_Z by lia; lia.

Lemma wr3_wr_sub : forall m A N, wr_at asegs m A N -> forall a n, A <= a -> a + n <= A + N -> wr_at asegs m a n.
Proof.
  intros m A N (W0 & W1 & W) a n X1 X2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + i) with (A + (a - A + i)) by lia. apply W. lia.
Qed.

Section WoR3.
  Context {HCEIL : HeapCeil}.

  Definition w2d_post (x2 gp tp x8 x19 x20 x24 : word) (F : bvmap 5 word) (fc : bv 32) (SP S1 ff tenv lo : Z) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS1_RA) x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 S1)
                    (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 0) (Z_to_bv 64 46) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) x19 x20 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 0x7fff8000) x24
                    (Z_to_bv 64 (ff + 3552)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
                F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3456, ff + 3497); (S1, S1 + 16); (S1 + 40, S1 + 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 3456) [C4 (Z_to_bv 64 tenv)]
      /\ rw_cells asegs m1 (ff + 3464) [C8 (Z_to_bv 64 (ff + 3376)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]
      /\ rw_cells asegs m1 S1 [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs m1 (S1 + 40) [C8 (Z_to_bv 64 0x7fff8000)].

  Lemma w2d : forall (x1 x2 gp tp x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x24 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (SP S1 ff tenv lo : Z),
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> lo <= S1 ->
    ff mod 64 = 0 -> 0x6e8000 + 0x9000 <= ff -> ff + 3808 <= S1 -> (sh ff + 476 <= ff \/ ff + 3808 <= sh ff) ->
    0 <= tenv < 19 ->
    rw_cells asegs m (ff + 3360) [C4 (Z_to_bv 64 tenv)] ->
    rw_cells asegs m (S1 + 48) [C8 (Z_to_bv 64 (ff + 2224)); C8 (Z_to_bv 64 (ff + 3376))] ->
    wr_at asegs m (ff + 3456) 48 -> u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) ->
    stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (w2d_post x2 gp tp x8 x19 x20 x24 F fc SP S1 ff tenv lo m)
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) x24 (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 (ff + 3360)) x28 x29 x30 x31) F (Z_to_bv 64 WO_PU) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros S1L S1H SPH LO F64 FLO FS1 FSH ENV CE CS WF US ST MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 (sh ff - 0x7fff8000)) by (apply sh_q; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 476 <= 0x10007fff8000)
      by (clear - FLO FS1 S1H SPH; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHB : SHBASE = 0x7fff8000) by reflexivity.
    assert (EF' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64))) = ff) by (rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES' : bv_unsigned (mul_div M_MUL (Z_to_bv 64 8) (Z_to_bv 64 (ff / 64))) = sh ff - 0x7fff8000) by (rewrite QS, u64_of_Z by lia; reflexivity).
    remember (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) x24 (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 (ff + 3360)) x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 0; Z_to_bv 64 S1; Z_to_bv 64 tenv]).
    assert (HR : regs_ok E (srs sr_id [(9%bv, EVar 34); (21%bv, EMd M_MUL (ELit 64) (EVar 32));
                   (22%bv, ELit 0); (23%bv, ELit 2147450880); (25%bv, ELit 0); (26%bv, ELit 0);
                   (27%bv, EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3360))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity).
      transitivity (Z_to_bv 64 (ff + 3360)); [reflexivity|]. rewrite Q, w_add by lia. reflexivity. }
    assert (HK : know_ok asegs E m
      [ KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 3360) 4 (EVar 35);
        KWord (SA (EVar 34) 48) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 2224));
        KWord (SA (EVar 34) 56) 8 (EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar 32)) (ELit 3376));
        KWord (SA (EMd M_MUL (ELit 8) (EVar 32)) (SHBASE + 433)) 1 (ELit 0);
        KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 3456) (ELit 48);
        KWr (SA (EVar 34) 0) (ELit 16);
        KWr (SA (EVar 34) 40) (ELit 8);
        KRange (EVar 32) ((0x6e8000 + 0x9000) / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47);
        KRange (EVar 35) 0 18 ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 3360) _ 0%nat (C4 (Z_to_bv 64 tenv))); [exact CE | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia | lia | cbn; lia | evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 0%nat (C8 (Z_to_bv 64 (ff + 2224)))); [exact CS | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 48) _ 8%nat (C8 (Z_to_bv 64 (ff + 3376)))); [exact CS | reflexivity | reflexivity | lia
                                 | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; cbn; lia | lia | cbn; lia | evs; rewrite Q, w_add by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword1_of_u8arr E m (sh ff) _ 433%nat); [exact US | vm_compute; reflexivity | lia | unfold estart; cbn [a_base a_off]; evs; rewrite ES'; unfold SHBASE; lia | lia | apply Nat.ltb_lt; vm_compute; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; evs; rewrite EF'; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite EF', u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; evs; rewrite u64_of_Z by lia; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_PU m (seg_rom asegs) HR HK 200%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { split_scs. all: cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia; unfold SHBASE; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rreg HR' 18%bv L18. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
    rreg HR' 25%bv L25. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; reflexivity).
    assert (L10' : getr R' 10 = Z_to_bv 64 (ff + 3504))
      by (rewrite L10, ?Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L18' : getr R' 18 = Z_to_bv 64 (ff + 3456))
      by (rewrite L18, ?Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L21' : getr R' 21 = Z_to_bv 64 ff) by (rewrite L21; exact Q).
    assert (L22' : getr R' 22 = Z_to_bv 64 (ff + 3504))
      by (rewrite L22, ?Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L25' : getr R' 25 = Z_to_bv 64 (ff + 3552))
      by (rewrite L25, ?Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (L27' : getr R' 27 = Z_to_bv 64 (ff + 2752))
      by (rewrite L27, ?Q; rewrite ?w_add, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
    assert (MU1 : munch [(ff + 3456, ff + 3497); (S1, S1 + 16); (S1 + 40, S1 + 48)] m M1).
    { subst M1. clear - Hlf F64 FLO FS1 SHL EF' ES' SHB S1L S1H SPH. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [a_base a_off]; rewrite ?EF', ?ES', ?u64_of_Z by lia;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
      apply Forall_nil. }
    assert (WSS : forall a n, S1 <= a -> a + n <= S1 + 48 -> wr_at asegs m a n).
    { intros a n X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (WFF : forall a n, ff + 3456 <= a -> a + n <= ff + 3504 -> wr_at asegs m a n).
    { intros a n X1 X2. destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (a + i) with (ff + 3456 + (a - (ff + 3456) + i)) by lia. apply W. lia. }
    assert (CP : rw_cells asegs M1 (ff + 3456) [C4 (Z_to_bv 64 tenv)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 S1L S1H SPH WFF Q.
      lgc Hlf 6%nat ltac:(djd EF' ES'). apply WFF; cbn; lia. }
    assert (CF : rw_cells asegs M1 (ff + 3464) [C8 (Z_to_bv 64 (ff + 3376)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (b8 0)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 S1L S1H SPH WFF Q.
      apply rw_cells_cons8_c; [lgc Hlf 4%nat ltac:(djd EF' ES'); [apply WFF; cbn; lia | HLib.evs; rewrite Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      apply rw_cells_cons8_c; [lgc Hlf 3%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      apply rw_cells_cons8_c; [lgc Hlf 2%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      apply rw_cells_cons8_c; [lgc Hlf 1%nat ltac:(djd EF' ES'); apply WFF; cbn; lia|].
      lgc Hlf 0%nat ltac:(djd EF' ES'). apply WFF; cbn; lia. }
    assert (CS2 : rw_cells asegs M1 S1 [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      apply rw_cells_cons8_c; [lgc Hlf 8%nat ltac:(djd EF' ES'); [apply WSS; cbn; lia | HLib.evs; rewrite Q, ?w_add, ?v_addi_Z by lia; reflexivity]|].
      lgc Hlf 7%nat ltac:(djd EF' ES'); [apply WSS; cbn; lia | HLib.evs; rewrite Q; reflexivity]. }
    assert (CS3 : rw_cells asegs M1 (S1 + 40) [C8 (Z_to_bv 64 0x7fff8000)]).
    { subst M1. clear - Hlf EF' ES' SHB SHL F64 FLO FS1 S1L S1H SPH WSS Q.
      lgc Hlf 5%nat ltac:(djd EF' ES'). apply WSS; cbn; lia. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1, L9', L10', L11, L12, L18', L21', L22', L23, L25', L26, L27'.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. split; [exact CP|]. split; [exact CF|]. split; [exact CS2 | exact CS3].
  Qed.

  Definition wr1_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS2_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3552)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 3552)) x26 x27
                    x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wr1 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr1_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS1_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 3552)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS1_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MS1_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 3552)) x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 3552))]) R) by wr3_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS1_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wr3_sc. }
    clear HK.
    wr3_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wr3_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS2_RA).
    wr3_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3552)).
    wr3_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wr3_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wr3_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = Z_to_bv 64 (ff + 3552)).
    assert (MU1 : munch [] m M1) by wr3_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L25.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.

  Definition wr2_post (x2 gp tp x8 x9 x19 x20 x21 x22 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS3_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3592)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456)) x19 x20 x21 x22 (Z_to_bv 64 0x3f800000)
                    x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3584, ff + 3588)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 3584) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wr2 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 3584) 4 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr2_post x2 gp tp x8 x9 x19 x20 x21 x22 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS2_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS2_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456))]) R) by wr3_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 3584) (ELit 4)]).
    { apply Forall_cons; [wr3_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS2_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wr3_sc. }
    clear HK.
    wr3_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wr3_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS3_RA).
    wr3_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3592)).
    wr3_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wr3_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wr3_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = Z_to_bv 64 (ff + 3456)).
    wr3_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    assert (MU1 : munch [(ff + 3584, ff + 3588)] m M1) by wr3_munch M1 Hlf.
    assert (CC : rw_cells asegs M1 (ff + 3584) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. lgc Hlf 0%nat wr3_dj; first [apply (wr3_wr_sub m (ff + 3584) 4 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L18, ?L23.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC.
  Qed.

  Definition wr3_post (x2 gp tp x8 x9 x19 x20 x21 x22 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS4_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3632)) (Z_to_bv 64 0)
                    (Z_to_bv 64 32) x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456)) x19 x20 x21 x22 (Z_to_bv 64 0x3f800000)
                    x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3624, ff + 3628)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 3624) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wr3 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 3624) 4 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr3_post x2 gp tp x8 x9 x19 x20 x21 x22 x24 x25 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS3_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS3_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS3_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (23%bv, ELit 1065353216)]) R) by wr3_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 3624) (ELit 4)]).
    { apply Forall_cons; [wr3_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS3_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wr3_sc. }
    clear HK.
    wr3_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wr3_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS4_RA).
    wr3_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3632)).
    wr3_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wr3_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 32).
    wr3_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = Z_to_bv 64 (ff + 3456)).
    wr3_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    assert (MU1 : munch [(ff + 3624, ff + 3628)] m M1) by wr3_munch M1 Hlf.
    assert (CC : rw_cells asegs M1 (ff + 3624) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. lgc Hlf 0%nat wr3_dj; first [apply (wr3_wr_sub m (ff + 3624) 4 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L18, ?L23.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC.
  Qed.

  Definition wr4_post (x2 gp tp x8 x9 x19 x20 x22 x24 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_MS5_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 0)
                    (Z_to_bv 64 72) x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456)) x19 x20 (Z_to_bv 64 (ff + 3720)) x22
                    (Z_to_bv 64 0x3f800000) x24 (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) x27 x28 x29 x30 x31)
               F (Z_to_bv 64 AASAN_MEMSET) fc None m1 (seg_rom asegs)
      /\ munch [(ff + 3664, ff + 3668)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (ff + 3664) [C4 (Z_to_bv 64 0x3f800000)].
  Lemma wr4 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> wr_at asegs m (ff + 3664) 4 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr4_post x2 gp tp x8 x9 x19 x20 x22 x24 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS4_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS4_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH WR ST MI.
    remember (mkR (Z_to_bv 64 WO_MS4_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3456))
               x19 x20 x21 x22 (Z_to_bv 64 0x3f800000) x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(18%bv, EAlu ALU_ADD (EVar 32) (ELit 3456)); (23%bv, ELit 1065353216)]) R) by wr3_seed R.
    assert (HK : know_ok asegs E m [KWr (SA (EVar 32) 3664) (ELit 4)]).
    { apply Forall_cons; [wr3_kwr WR|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS4_RA m (seg_rom asegs) HR HK 20%nat [AASAN_MEMSET] (SCR [] [] []) 40%N.
    { wr3_sc. }
    clear HK.
    wr3_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wr3_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_MS5_RA).
    wr3_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3672)).
    wr3_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 0).
    wr3_r HR' HR0 (12%bv : reg) L12 (getr R' 12 = Z_to_bv 64 72).
    wr3_r HR' HR0 (18%bv : reg) L18 (getr R' 18 = Z_to_bv 64 (ff + 3456)).
    wr3_r HR' HR0 (21%bv : reg) L21 (getr R' 21 = Z_to_bv 64 (ff + 3720)).
    wr3_r HR' HR0 (23%bv : reg) L23 (getr R' 23 = Z_to_bv 64 0x3f800000).
    wr3_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = Z_to_bv 64 (ff + 3672)).
    wr3_r HR' HR0 (26%bv : reg) L26 (getr R' 26 = Z_to_bv 64 (ff + 3696)).
    assert (MU1 : munch [(ff + 3664, ff + 3668)] m M1) by wr3_munch M1 Hlf.
    assert (CC : rw_cells asegs M1 (ff + 3664) [C4 (Z_to_bv 64 0x3f800000)]).
    { subst M1. lgc Hlf 0%nat wr3_dj; first [apply (wr3_wr_sub m (ff + 3664) 4 WR); cbn; lia | evs; reflexivity]. }
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L12, ?L18, ?L21, ?L23, ?L25, ?L26.
    apply evt_done.
    do 12 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|]. exact CC.
  Qed.

  Definition wr5_post (x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      (ff lo SP : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 WO_ON1_RA) x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 25)
                    x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (ff + 3672)) x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xec4ac) fc None m1 (seg_rom asegs)
      /\ munch [] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP.
  Lemma wr5 : forall (x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28
                      x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ff lo SP : Z),
    0 <= ff -> ff + 3808 <= 2 ^ 47 -> stk asegs m lo SP -> mem_inv asegs m ->
    evt asegs (wr5_post x2 gp tp x8 x9 x18 x19 x20 x21 x22 x23 x24 x26 x27 F fc ff lo SP m)
      (MS (mkR (Z_to_bv 64 WO_MS5_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 3672)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 WO_MS5_RA) fc None m (seg_rom asegs)).
  Proof.
    intros x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 F fc m ff lo SP F0 FH ST MI.
    remember (mkR (Z_to_bv 64 WO_MS5_RA) x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
               x24 (Z_to_bv 64 (ff + 3672)) x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ff]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EAlu ALU_ADD (EVar 32) (ELit 3672))]) R) by wr3_seed R.
    assert (HK : know_ok asegs E m []) by apply Forall_nil.
    xrun_at (PropExec.mkFP F fc) asegs R WO_MS5_RA m (seg_rom asegs) HR HK 20%nat [0xec4ac] (SCR [] [] []) 40%N.
    { wr3_sc. }
    clear HK.
    wr3_mem E m Hlf Hms M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    wr3_r HR' HR0 (1%bv : reg) L1 (getr R' 1 = Z_to_bv 64 WO_ON1_RA).
    wr3_r HR' HR0 (10%bv : reg) L10 (getr R' 10 = Z_to_bv 64 (ff + 3672)).
    wr3_r HR' HR0 (11%bv : reg) L11 (getr R' 11 = Z_to_bv 64 25).
    wr3_r HR' HR0 (25%bv : reg) L25 (getr R' 25 = Z_to_bv 64 (ff + 3672)).
    assert (MU1 : munch [] m M1) by wr3_munch M1 Hlf.
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, ?L1, ?L10, ?L11, ?L25.
    apply evt_done.
    do 13 eexists; exists M1; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    subst M1; apply stk_mem_denot; exact ST.
  Qed.
End WoR3.
