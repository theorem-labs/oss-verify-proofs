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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition PT_SM_RET : Z := 0xfeb38.
Definition PT_HEAD : Z := 0xfec68.
Definition PT_SKIP : Z := 0xfec50.
Definition PT_AN_RET : Z := 0xfed38.
Definition PT_SL_RET : Z := 0xfed6c.
Definition PT_EXIT : Z := 0xfee64.
Definition PT_RET : Z := 0xfef08.

Lemma pt_sllk : forall a k, 0 <= k < 64 -> alu64 ALU_SLL (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a * 2 ^ k).
Proof.
  intros a k Hk. apply bv_eq. rewrite u_sll64, !u_lit64a.
  rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k 64) by lia.
  rewrite Zmult_mod_idemp_l. reflexivity.
Qed.

Section PT1.
  Context {HCEIL : HeapCeil}.

  Definition pt1_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SP S1 ps v lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 64)
                    x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 s10 s11
                    x28 x29 x30 x31) F (Z_to_bv 64 AFS_MALLOC_0) fc None m1 (seg_rom asegs)
      /\ munch [(SP - 192, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 (S1 + 40) [C8 (Z_to_bv 64 v)].

  Lemma pt_b1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ps v lo : Z),
    a0 = Z_to_bv 64 ps -> 0 <= ps < 2 ^ 64 -> a1 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 256 ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (pt1_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp)
                 (bv_unsigned sp - 192 - bv_unsigned sp mod 32) ps v lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AT_PUSH_TYPES) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros Ha0 Hps Ha1 Hv SP16 SPR ST CE LO MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (Hq : spz = 32 * (spz / 32) + spz mod 32) by (Z.div_mod_to_equations; lia).
    assert (Hr : spz mod 32 = 0 \/ spz mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    set (q := spz / 32) in *. set (r := spz mod 32) in *. clearbody q r.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose proof (ACONST_shbase m AC) as [CG CS]. pose proof (ACONST_uar m AC) as [CU CU1].
    pose (E := Eseed R [Z_to_bv 64 ps; Z_to_bv 64 q; Z_to_bv 64 v]).
    assert (HK : know_ok asegs E m
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (ELit 0) AGOT_UAR) 8 (ELit AUAR_CELL);
         KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
         KWr (SA (EMd M_MUL (ELit 32) (EVar 33)) (r - 192)) (ELit 192);
         KRange (EVar 33) (2 ^ 40) (2 ^ 42) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850f8 _ 0%nat (C8 (wz AUAR_CELL))); [exact CU | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191040 _ 0%nat (C4 (wz 1))); [exact CU1 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite w_mul, u64_of_Z by lia; cbn [a_off]; lia
                           | unfold estart, elenZ; evs; rewrite w_mul, !u64_of_Z by lia; cbn [a_off]; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    assert (HB : bv_unsigned (edenot E (EMd M_MUL (ELit 32) (EVar 33))) = 32 * q) by (evs; rewrite w_mul, u64_of_Z by lia; reflexivity).
    assert (WS : forall a, spz - 192 <= a -> a + 8 <= spz -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    destruct Hr as [Hr | Hr]; rewrite Hr in *;
      [ assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EMd M_MUL (ELit 32) (EVar 33)); (11%bv, EVar 34)]) R)
          by (apply regs_ok_srs; [apply regs_ok_seed|];
              repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | | exact Ha1];
              rewrite w_mul by lia; transitivity sp; [reflexivity|]; rewrite Hsp; f_equal; lia);
        xrun_at (PropExec.mkFP F fc) asegs R AT_PUSH_TYPES m (seg_rom asegs) HR HK 100%nat [AFS_MALLOC_0] (SCR [] [] []) 40%N;
        [ split_scs | ]
      | assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 33)) (ELit 16)); (11%bv, EVar 34)]) R)
          by (apply regs_ok_srs; [apply regs_ok_seed|];
              repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | | exact Ha1];
              rewrite w_mul, w_add by lia; transitivity sp; [reflexivity|]; rewrite Hsp; f_equal; lia);
        xrun_at (PropExec.mkFP F fc) asegs R AT_PUSH_TYPES m (seg_rom asegs) HR HK 100%nat [AFS_MALLOC_0] (SCR [] [] []) 40%N;
        [ split_scs | ] ].
    all: clear HK.
    all: lazymatch type of Hlf with log_flat _ ?lg =>
           lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
             change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    all: assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    all: pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    all: readback HR' HF1 HR0 HRe.
    all: rreg HR' 1%bv L1; rreg HR' 2%bv L2; rreg HR' 8%bv L8; rreg HR' 9%bv L9; rreg HR' 10%bv L10; rreg HR' 18%bv L18; rreg HR' 24%bv L24.
    all: rewrite ?w_mul in L2, L8, L9 by lia; rewrite ?w_add in L8 by lia; rewrite ?w_addm in L2, L9 by lia.
    all: assert (MU1 : munch [(spz - 192, spz)] m M1)
           by (subst M1; clear - Hlf HB Hq SPR Hr;
               pose proof (munch_mem_denot_sb [(r - 192, r)] (EMd M_MUL (ELit 32) (EVar 33)) _ m _ Hlf ltac:(rewrite Hr; vm_compute; reflexivity)) as MU;
               rewrite HB in MU; cbn [map fst snd] in MU; eapply munch_eqW; [exact MU | repeat f_equal; lia]).
    all: assert (CF1 : rw_cells asegs M1 (spz - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (subst M1; clear - Hlf HB Hq SPR WS HR0;
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 1%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 2%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 3%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 4%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 5%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 6%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 7%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 8%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 9%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 10%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 11%nat|];
              apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 12%nat|];
              lgcell2 Hlf HB WS 13%nat).
    all: assert (CF3 : rw_cells asegs M1 (spz - 192 - r + 40) [C8 (Z_to_bv 64 v)])
           by (subst M1; clear - Hlf HB Hq SPR WS HR0 Hr; lgcell2 Hlf HB WS 0%nat).
    all: assert (L2' : getr R' 2 = Z_to_bv 64 (spz - 192 - r)) by (rewrite L2; f_equal; lia).
    all: assert (L9' : getr R' 9 = Z_to_bv 64 (spz - 192 - r)) by (rewrite L9; f_equal; lia).
    all: assert (L8' : getr R' 8 = Z_to_bv 64 spz) by (rewrite L8; f_equal; lia).
    all: rewrite Hr in L2', L9'.
    all: eapply evt_of_msteps; [exact Hms|].
    all: rewrite mkst_MS, HRe, L1, L2', L8', L9', L10, L18, L24.
    all: apply evt_done.
    all: do 15 eexists; split; [reflexivity|].
    all: split; [exact MU1|]; split; [subst M1; apply wmono_mem_denot|]; split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    all: split; [subst M1; apply stk_mem_denot; exact ST|]. all: split; [exact CF1|].
    all: rewrite Hr in CF3; exact CF3.
  Qed.

  Definition PT_B2M : Z := 0xfebd0.

  Lemma pt_b2a : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (gp tp s3 s4 s5 s6 s7 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff SP S1 ps v lo : Z),
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> 0 <= ps < 2 ^ 64 ->
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    wr_at asegs m ff 64 -> wr_at asegs m (sh ff) 8 -> stk asegs m lo SP -> lo <= S1 -> ff + 64 <= lo ->
    rw_cells asegs m (S1 + 40) [C8 (Z_to_bv 64 v)] ->
    relro0 m -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 s10 s11
                 x28 x29 x30 x31) F (Z_to_bv 64 PT_SM_RET) fc None m ro)
        (MS R' F (Z_to_bv 64 PT_B2M) fc None M' ro)
      /\ R' = mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ps + 8))
                 (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (Z_to_bv 64 ff) (Z_to_bv 64 v) x17
                 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 (Z_to_bv 64 (sh ff)) s11 x28 x29 x30 x31
      /\ munch [(S1, S1 + 8); (ff, ff + 24); (sh ff, sh ff + 8)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ stk asegs M' lo SP /\ rw_cells asegs M' S1 [C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs M' (sh ff + 4) [C1 (b8 0xf8)].
  Proof.
    intros until lo. intros F64 FLO FHI Hps S32 S45 SS SPH WF WS ST LO FLOW CS RR MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
    assert (SHL : 0x7fff8000 <= sh ff < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    remember (mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 ff)
                 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 s10 s11
                 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 S1; Z_to_bv 64 ps; Z_to_bv 64 v]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EMd M_MUL (ELit 64) (EVar 32)); (9%bv, EVar 33); (18%bv, ELit 2147450880); (24%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity. rewrite Q. reflexivity. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
      by (evs; rewrite w_mul by (Z.div_mod_to_equations; lia); rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 33) 40) 8 (EVar 35);
         KImg 0x17e000 0x186000;
         KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 64);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
         KWr (SA (EVar 33) 0) (ELit 8);
         KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41); KRange (EVar 33) (2 ^ 45) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CS 0%nat (C8 (Z_to_bv 64 v)). }
      apply Forall_cons. { apply kimg_relro; exact RR. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
                                  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PT_SM_RET m ro HR HK 200%nat [PT_B2M] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 15%bv L15. rreg HR' 16%bv L16.
    rreg HR' 18%bv L18. rreg HR' 24%bv L24. rreg HR' 26%bv L26.
    assert (QS' : 8 * (ff / 64) + 2147450880 = sh ff) by (rewrite <- QS; reflexivity).
    split.
    { rewrite HRe at 1. rewrite ?L1, ?L2, ?L9, ?L10, ?L15, ?L16, ?L18, ?L24, ?L26. rewrite TablLib.zbv_add, Q.
      rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
      rewrite QS'. subst R. reflexivity. }
    split.
    { subst M1. clear - Hlf F64 FLO FHI S45 SS SPH SHL QS QS' Q EF ES EP FLOW LO. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                  first [rewrite EF | rewrite ES | rewrite EP];
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].
    split.
    { subst M1. eapply (rw_cells_log_nth _ m _ 11%nat); [exact Hlf | reflexivity | | | | reflexivity | exact I | evs; rewrite Q; reflexivity].
      - repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                    rewrite ?EF, ?ES, ?EP; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                                    unfold SHBASE in *; lia|]).
        apply Forall_nil.
      - unfold estart. cbn [a_base a_off]. rewrite EP. lia.
      - pose proof (wr_at_of_stk asegs m lo SP ST) as W. destruct W as (W1 & W2 & W).
        split; [lia|]. split; [lia|]. intros i Hi. replace (S1 + i) with (lo + (S1 - lo + i)) by lia. apply W. cbn in Hi. lia. }
    subst M1. eapply (rw_cells_log_nth _ m _ 7%nat); [exact Hlf | reflexivity | | | | reflexivity | exact I |].
    - repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                  rewrite ?EF, ?ES, ?EP; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                                  unfold SHBASE in *; lia|]).
      apply Forall_nil.
    - unfold estart. cbn [a_base a_off]. rewrite ES. unfold SHBASE in *. lia.
    - destruct WS as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros j Hj. replace (sh ff + 4 + j) with (sh ff + (4 + j)) by lia.
      apply W. cbn in Hj. lia.
    - first [reflexivity | evs; cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity].
  Qed.

  Lemma sh_word : forall x, 0 <= x < 2 ^ 64 ->
    alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (sh x).
  Proof.
    intros x Hx. rewrite HWord.w_srl by lia. rewrite TablLib.zbv_add. f_equal. unfold sh. rewrite ASHADOW_BASE_val.
    change (2 ^ 3) with 8. lia.
  Qed.

#[local] Definition HTATablPT1_0 : list (reg * expr) := [(10%bv, EAlu ALU_ADD (EVar 32) (ELit 8)); (15%bv, EMd M_MUL (ELit 64) (EVar 36)); (16%bv, EVar 34); (18%bv, ELit 2147450880); (24%bv, EVar 32); (9%bv, EVar 33)].
  Lemma pt_b2b : forall (x5 x6 x7 x11 x12 x13 x14 x17 x28 x29 x30 x31 : word) (gp tp s3 s4 s5 s6 s7 s9 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff SP S1 ps v n lo : Z),
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> 0 <= ps -> ps + 16 <= 2 ^ 47 -> ps mod 8 = 0 ->
    0 < v -> v mod 8 = 0 -> v + 24 <= 2 ^ 47 -> 0 <= n <= 48 ->
    S1 mod 32 = 0 -> 2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 ->
    stk asegs m lo SP -> lo <= S1 ->
    rw_cells asegs m (ps + 8) [C8 (Z_to_bv 64 n)] -> sh0 m (ps + 8) ->
    (ps + 16 <= S1 \/ S1 + 88 <= ps) ->
    mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs
        (MS (mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ps + 8))
                 x11 x12 x13 x14 (Z_to_bv 64 ff) (Z_to_bv 64 v) x17
                 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 (Z_to_bv 64 (sh ff)) s11 x28 x29 x30 x31) F (Z_to_bv 64 PT_B2M) fc None m ro)
        (MS R' F (Z_to_bv 64 (if n =? 0 then PT_EXIT else PT_HEAD)) fc None M' ro)
      /\ munch [(S1 + 8, S1 + 40); (S1 + 48, S1 + 64); (S1 + 80, S1 + 88)] m M' /\ wmono asegs m M' /\ mem_inv asegs M' /\ stk asegs M' lo SP
      /\ rw_cells asegs M' (S1 + 8) [C8 (Z_to_bv 64 ff)] /\ rw_cells asegs M' (S1 + 80) [C8 (Z_to_bv 64 ff)]
      /\ getr R' 2 = Z_to_bv 64 S1 /\ getr R' 8 = Z_to_bv 64 SP /\ getr R' 9 = Z_to_bv 64 S1 /\ getr R' 26 = Z_to_bv 64 (sh ff)
      /\ getr R' 1 = Z_to_bv 64 PT_SM_RET /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 24 = Z_to_bv 64 ps /\ getr R' 25 = s9
      /\ (n <> 0 ->
           rw_cells asegs M' (S1 + 16) [C8 (Z_to_bv 64 (sh v)); C8 (Z_to_bv 64 (sh (v + 16))); C8 (Z_to_bv 64 (v + 16))]
           /\ rw_cells asegs M' (S1 + 48) [C8 (Z_to_bv 64 (2 ^ 61)); C8 (Z_to_bv 64 (sh ps))]
           /\ getr R' 10 = Z_to_bv 64 0 /\ getr R' 11 = Z_to_bv 64 4 /\ getr R' 12 = Z_to_bv 64 (sh (v + 16))
           /\ getr R' 13 = Z_to_bv 64 (2 ^ 61) /\ getr R' 15 = Z_to_bv 64 ff /\ getr R' 16 = Z_to_bv 64 v
           /\ getr R' 18 = Z_to_bv 64 0x7fff8000 /\ getr R' 19 = Z_to_bv 64 (sh ps) /\ getr R' 20 = Z_to_bv 64 1
           /\ getr R' 21 = Z_to_bv 64 (v + 8) /\ getr R' 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R' 23 = Z_to_bv 64 (ff + 32)
           /\ getr R' 27 = Z_to_bv 64 n).
  Proof.
    intros until lo. intros F64 FLO FHI P0 P16 P8 V0 V8 V24 Hn S32 S45 SS SPH ST LO CN SHP PD MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    remember (mkR (Z_to_bv 64 PT_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 (ps + 8))
                 x11 x12 x13 x14 (Z_to_bv 64 ff) (Z_to_bv 64 v) x17
                 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 (Z_to_bv 64 ps) s9 (Z_to_bv 64 (sh ff)) s11 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 ps; Z_to_bv 64 S1; Z_to_bv 64 v; Z_to_bv 64 n; Z_to_bv 64 (ff / 64)]).
    assert (HR : regs_ok E (srs sr_id HTATablPT1_0) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs;
        try reflexivity; try (rewrite Q; reflexivity). rewrite TablLib.zbv_add. reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       (kn_fix 4 [PT_HEAD; PT_EXIT] (SCR [false] [] []) PT_B2M
          (srs sr_id HTATablPT1_0)
          [ KWord (SA (EVar 32) 8) 8 (EVar 35);
            KWr (SA (EVar 33) 8) (ELit 80);
            KRange (EVar 35) 0 48; KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0 (2 ^ 47 - 16);
            KRange (EVar 34) 1 (2 ^ 47 - 24); KAlign (EVar 34) 8; KRange (EVar 36) (0x6e8000 / 64) (2 ^ 41);
            KDisj (SA (EVar 32) 8) (ELit 8) (SA (EVar 33) 8) (ELit 80) ] 37)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ps + 8) _ 0%nat (C8 (Z_to_bv 64 n))); [exact CN | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      do 6 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia|]).
      apply Forall_cons. { cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. evs. rewrite !u64_of_Z by lia. lia. }
      apply Forall_cons; [|apply Forall_nil].
      eapply (kshadow0 _ _ _ (ps + 8)); [evs; rewrite TablLib.zbv_add; reflexivity | lia | exact SHP]. }
    assert (HB : bv_unsigned (edenot E (EVar 33)) = S1) by exact EP.
    assert (WS : forall a, S1 + 8 <= a -> a + 8 <= S1 + 88 -> wr_at asegs m a 8).
    { intros a Ha1 Ha2. pose proof (wr_at_of_stk asegs m lo SP ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    Ltac lgc Hlf HB WS k :=
      eapply (rw_cells_log_nth_sb _ _ _ k);
      [ exact Hlf | reflexivity | vm_cast_no_check (@eq_refl bool true) | rewrite HB; lia
      | apply WS; lia | reflexivity | exact I
      | first [ reflexivity
              | HLib.evs; rewrite ?TablLib.zbv_add; rewrite ?sh_word by lia; reflexivity
              | HLib.evs; match goal with QQ : mul_div M_MUL (Z_to_bv 64 64) _ = _ |- _ => rewrite QQ; reflexivity end
              | HLib.evs; match goal with HRx : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite HRx; reflexivity end ] ].
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    destruct (Z.eqb_spec n 0) as [N0|N0].
    -
      xrun_at (PropExec.mkFP F fc) asegs R PT_B2M m ro HR HK 100%nat [PT_HEAD; PT_EXIT] (SCR [true] [] []) 37%N.
      { split_scs; try sc_dj. cbn [sc_denot]. subst E. evs. rewrite br_eq by lia. rewrite N0. reflexivity. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
      readback HR' HF1 HR0 HRe.
      split; [subst M1; pose proof (munch_mem_denot_sb [(8, 40); (48, 64); (80, 88)] (EVar 33) E m _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
              rewrite HB in MU; cbn [map fst snd] in MU; exact MU|].
      split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [subst M1; apply stk_mem_denot; exact ST|].
      split; [subst M1; lgc Hlf HB WS 1%nat|]. split; [subst M1; lgc Hlf HB WS 0%nat|].
      rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 3%bv L3. rreg HR' 4%bv L4. rreg HR' 8%bv L8. rreg HR' 9%bv L9.
      rreg HR' 24%bv L24. rreg HR' 25%bv L25. rreg HR' 26%bv L26.
      subst R. rewrite L2, L8, L9, L26, L1, L3, L4, L24, L25.
      repeat (split; [reflexivity|]). intros C; exfalso; exact (C N0).
    -
      xrun_at (PropExec.mkFP F fc) asegs R PT_B2M m ro HR HK 100%nat [PT_HEAD; PT_EXIT] (SCR [false] [] []) 37%N.
      { split_scs; try sc_dj. cbn [sc_denot]. subst E. evs. rewrite br_eq by lia. apply Z.eqb_neq. exact N0. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
      readback HR' HF1 HR0 HRe.
      split; [subst M1; pose proof (munch_mem_denot_sb [(8, 40); (48, 64); (80, 88)] (EVar 33) E m _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
              rewrite HB in MU; cbn [map fst snd] in MU; exact MU|].
      split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [subst M1; apply stk_mem_denot; exact ST|].
      split; [subst M1; lgc Hlf HB WS 6%nat|]. split; [subst M1; lgc Hlf HB WS 5%nat|].
      rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 3%bv L3. rreg HR' 4%bv L4. rreg HR' 8%bv L8. rreg HR' 9%bv L9.
      rreg HR' 24%bv L24. rreg HR' 25%bv L25. rreg HR' 26%bv L26.
      rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13. rreg HR' 15%bv L15. rreg HR' 16%bv L16.
      rreg HR' 18%bv L18. rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23.
      rreg HR' 27%bv L27.
      subst R. rewrite L2, L8, L9, L26, L1, L3, L4, L24, L25.
      repeat (split; [reflexivity|]). intros _.
      split; [subst M1; apply rw_cells_cons8_c; [lgc Hlf HB WS 1%nat | apply rw_cells_cons8_c; [lgc Hlf HB WS 0%nat | lgc Hlf HB WS 2%nat]]|].
      split; [subst M1; apply rw_cells_cons8_c; [lgc Hlf HB WS 4%nat | lgc Hlf HB WS 3%nat]|].
      split; [rewrite L10; reflexivity|]. split; [rewrite L11; reflexivity|].
      split; [rewrite L12, TablLib.zbv_add, sh_word by lia; reflexivity|]. split; [rewrite L13; reflexivity|].
      split; [rewrite L15, Q; reflexivity|]. split; [rewrite L16; reflexivity|]. split; [rewrite L18; reflexivity|].
      split; [rewrite L19, sh_word by lia; reflexivity|]. split; [rewrite L20; reflexivity|].
      split; [rewrite L21, TablLib.zbv_add; reflexivity|]. split; [rewrite L22, TablLib.zbv_add, sh_word by lia; reflexivity|].
      split; [rewrite L23, Q, TablLib.zbv_add; reflexivity|].
      rewrite L27. reflexivity.
  Qed.
End PT1.
