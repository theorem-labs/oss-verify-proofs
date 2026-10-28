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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_PrsStmt LbB_DiagStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition EX_SM_RA : Z := 0xf8c78.

Section ExR1.
  Context {HCEIL : HeapCeil}.

  Definition x1_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SP S1 this ioff opc ty lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 EX_SM_RA) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 512)
                    x11 x12 x13 x14 x15 x16 x17 s2 s3 (Z_to_bv 64 ioff) s5 (Z_to_bv 64 ty) (Z_to_bv 64 this) (Z_to_bv 64 opc)
                    s9 (Z_to_bv 64 0x7fff8000) s11 x28 x29 x30 x31) F (Z_to_bv 64 AFS_MALLOC_3) fc None m1 (seg_rom asegs)
      /\ munch [(S1, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition x1_sr (r : Z) : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35);
    (2%bv, EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 36)) (ELit r))].
  Definition x1_kn (r : Z) : list kentry :=
    [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
      KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
      KWord (SA (ELit 0) AGOT_UAR) 8 (ELit AUAR_CELL);
      KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
      KWr (SA (EMd M_MUL (ELit 32) (EVar 36)) (r - 192)) (ELit 192);
      KRange (EVar 36) (2 ^ 40) (2 ^ 42) ].

  Lemma x1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (this ioff opc ty lo : Z),
    a0 = Z_to_bv 64 this -> a1 = Z_to_bv 64 ioff -> a2 = Z_to_bv 64 opc -> a3 = Z_to_bv 64 ty ->
    0 <= this < 2 ^ 64 -> 0 <= ioff < 2 ^ 64 -> 0 <= opc < 2 ^ 64 -> 0 <= ty < 2 ^ 64 ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 512 ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (x1_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp)
                 (bv_unsigned sp - 128 - bv_unsigned sp mod 32) this ioff opc ty lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AEXHAUSTED) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros Ha0 Ha1 Ha2 Ha3 HC HW HN HT SP16 SPR ST LO MI AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hq : spz = 32 * (spz / 32) + spz mod 32) by (Z.div_mod_to_equations; lia).
    assert (Hr : spz mod 32 = 0 \/ spz mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    set (q := spz / 32) in *. set (r := spz mod 32) in *. clearbody q r.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose proof (ACONST_shbase m AC) as [CG CS]. pose proof (ACONST_uar m AC) as [CU CU1].
    pose (E := Eseed R [Z_to_bv 64 this; Z_to_bv 64 ioff; Z_to_bv 64 opc; Z_to_bv 64 ty; Z_to_bv 64 q]).
    assert (HB : bv_unsigned (edenot E (EMd M_MUL (ELit 32) (EVar 36))) = 32 * q) by (evs; rewrite w_mul, u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m (x1_kn r)).
    { unfold know_ok, x1_kn.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850f8 _ 0%nat (C8 (wz AUAR_CELL))); [exact CU | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191040 _ 0%nat (C4 (wz 1))); [exact CU1 | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite HB; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; rewrite HB; evs; rewrite u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    assert (WS : forall a, spz - 192 <= a -> a + 8 <= spz -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    assert (HSP : edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 32) (EVar 36)) (ELit r)) = sp).
    { evs. rewrite w_mul by lia. destruct Hr as [Hr|Hr]; rewrite Hr; rewrite w_add by lia; rewrite Hsp; f_equal; lia. }
    assert (HR : regs_ok E (x1_sr r) R).
    { unfold x1_sr. apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [split; [cbn [fst]; intros X; discriminate X | cbn [fst snd]; rewrite HR0;
        first [ exact (eq_sym HSP) | evs; first [ reflexivity | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 ] ] ] |]);
      apply Forall_nil. }
    destruct Hr as [Hr|Hr]; rewrite Hr in HK, HR |- *; cbn iota;
      [ xrun_at (PropExec.mkFP F fc) asegs R AEXHAUSTED m (seg_rom asegs) HR HK 200%nat [AFS_MALLOC_3] (SCR [] [] []) 40%N
      | xrun_at (PropExec.mkFP F fc) asegs R AEXHAUSTED m (seg_rom asegs) HR HK 200%nat [AFS_MALLOC_3] (SCR [] [] []) 40%N ];
      [ split_scs | | split_scs | ].
    all: clear HK.
    all: lazymatch type of Hlf with log_flat _ ?lg =>
           lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
             change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    all: assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    all: pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    all: readback HR' HF1 HR0 HRe.
    all: rreg HR' 1%bv L1; rreg HR' 2%bv L2; rreg HR' 8%bv L8; rreg HR' 9%bv L9; rreg HR' 10%bv L10; rreg HR' 20%bv L20;
         rreg HR' 22%bv L22; rreg HR' 23%bv L23; rreg HR' 24%bv L24; rreg HR' 26%bv L26.
    all: rewrite ?w_mul in L2, L8, L9 by lia; rewrite ?w_add in L8 by lia; rewrite ?w_addm in L2, L9 by lia.
    all: assert (L2' : getr R' 2 = Z_to_bv 64 (spz - 128 - r)) by (rewrite L2; f_equal; lia).
    all: assert (L9' : getr R' 9 = Z_to_bv 64 (spz - 128 - r)) by (rewrite L9; f_equal; lia).
    all: assert (L8' : getr R' 8 = Z_to_bv 64 spz) by (first [rewrite L8; f_equal; lia | rewrite L8, Hq, Hr; f_equal; lia]).
    all: rewrite Hr in L2', L9'.
    all: assert (MU1 : munch [(spz - 128 - r, spz)] m M1)
           by (subst M1; clear - Hlf HB Hq SPR Hr;
              pose proof (munch_mem_denot_sb [(-128, r)] (EMd M_MUL (ELit 32) (EVar 36)) _ m _ Hlf ltac:(rewrite Hr; vm_compute; reflexivity)) as MU;
               rewrite HB in MU; cbn [map fst snd] in MU; eapply munch_eqW; [exact MU | rewrite Hr; repeat f_equal; lia]).
    all: rewrite Hr in MU1.
    all: assert (CF1 : rw_cells asegs M1 (spz - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (subst M1; clear - Hlf HB Hq SPR WS HR0 Hr;
               apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 0%nat|];
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
               lgcell2 Hlf HB WS 12%nat).
    all: eapply evt_of_msteps; [exact Hms|].
    all: rewrite mkst_MS, HRe, L1, L2', L8', L9', L10, L20, L22, L23, L24, L26.
    all: apply evt_done.
    all: do 15 eexists; split; [reflexivity|].
    all: split; [exact MU1|]; split; [subst M1; apply wmono_mem_denot|]; split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    all: split; [subst M1; apply stk_mem_denot; exact ST | exact CF1].
  Qed.
End ExR1.
