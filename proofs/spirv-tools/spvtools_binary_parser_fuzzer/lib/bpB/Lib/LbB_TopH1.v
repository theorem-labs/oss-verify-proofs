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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TOP_ENTRY : Z := 0xe8894.
Definition TOP_SM_RET : Z := 0xe890c.
Definition TOP_H1_MID : Z := 0xe88f8.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 (-32)) = Z_to_bv 64 (x - x mod 32).
Proof.
  intros x Hx. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as HM.
  rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small (x - x mod 32)) by (Z.div_mod_to_equations; lia).
  rewrite <- (Z.land_ones (-32) 64) by lia. rewrite Z.land_assoc. rewrite Z.land_ones by lia.
  change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

Lemma h1_srl5 : forall a, 0 <= a < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 5) = Z_to_bv 64 (a / 32).
Proof.
  intros a Ha. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a) by lia.
  replace (bv_unsigned (bv_and (Z_to_bv 64 5) (Z_to_bv 64 63))) with 5 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  rewrite Z.mod_small by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Ltac h1_ar := rewrite ?w_addm, ?w_add by lia; rewrite ?h1_srl5 by lia; rewrite ?w_mul by (Z.div_mod_to_equations; lia);
  rewrite ?land_m32 by (Z.div_mod_to_equations; lia); rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia).

Ltac h1_rwc1 Hlf HR0 WW :=
  let t k := (eapply (rw_cells_log_nth _ _ _ k);
               [ exact Hlf | reflexivity | idtac | unfold estart; cbn [a_base a_off]; evs; h1_ar; Z.div_mod_to_equations; lia
               | idtac | reflexivity | exact I | cbn [cbytes]; evs; rewrite ?HR0; reflexivity ]);
             [ cbn [firstn]; repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; h1_ar;
                                                       Z.div_mod_to_equations; lia |]); apply Forall_nil
             | apply WW; Z.div_mod_to_equations; lia ] in
  first [ t 0%nat | t 1%nat | t 2%nat | t 3%nat | t 4%nat | t 5%nat | t 6%nat | t 7%nat | t 8%nat | t 9%nat
        | t 10%nat | t 11%nat | t 12%nat | t 13%nat | t 14%nat | t 15%nat | t 16%nat | t 17%nat | t 18%nat | t 19%nat ].

Section TopH1.
  Context {HCEIL : HeapCeil}.

  Definition h1a_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SP S1 D N lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1,
      ms' = MS (mkR (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 S1) (Z_to_bv 64 2752)
                    x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 0x7fff8000) s6 s7 s8 s9 s10 (Z_to_bv 64 N)
                    x28 x29 x30 x31) F (Z_to_bv 64 AFS_MALLOC_6) fc None m1 (seg_rom asegs)
      /\ munch [(SP - 224, SP)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
      /\ rw_cells asegs m1 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m1 (S1 + 88) [C8 (Z_to_bv 64 D)].

  Lemma h1a : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (D N lo : Z),
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N -> 0 <= D < 2 ^ 64 -> 0 <= N < 2 ^ 26 ->
    bv_unsigned sp mod 16 = 0 -> 2 ^ 45 <= bv_unsigned sp <= 2 ^ 47 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 4096 ->
    mem_inv asegs m -> ACONST m ->
    evt asegs (h1a_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp)
                 (bv_unsigned sp - 224 - bv_unsigned sp mod 32) D N lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 TOP_ENTRY) fc None m (seg_rom asegs)).
Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D N lo
      HA0 HA1 DR NR SP16 SPR ST LOC LOS MI AC.
    subst a0 a1.
    set (SP := bv_unsigned sp) in *.
    assert (HSP : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    clearbody SP. subst sp.
    set (S1 := SP - 224 - SP mod 32).
    assert (S1F : S1 mod 32 = 0 /\ SP - 255 <= S1 <= SP - 224) by (subst S1; Z.div_mod_to_equations; lia).
    assert (WW : forall a n, lo <= a -> a + n <= SP -> 0 <= n -> wr_at asegs m a n).
    { intros a n H1 H2 H3. destruct (stk_split asegs m lo a SP ST ltac:(lia)) as [_ S2].
      destruct (stk_split asegs m a (a + n) SP S2 ltac:(lia)) as [S3 _].
      pose proof (wr_at_of_stk asegs m a (a + n) S3) as W. replace (a + n - a) with n in W by lia. exact W. }
    remember (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 N) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 0; Z_to_bv 64 SP; Z_to_bv 64 D; Z_to_bv 64 N]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 33); (10%bv, EVar 34); (11%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor.
      all: cbn [fst snd]; try (intros X; discriminate X).
      all: subst R; evs; reflexivity. }
    assert (EP : bv_unsigned (edenot E (EVar 33)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    destruct (ACONST_shbase m AC) as [G1 G2]. destruct (ACONST_uar m AC) as [G3 G4].
    assert (HK : know_ok asegs E m [KWord (SA (ELit 0) 1593504) 8 (ELit 1642552); KWord (SA (ELit 0) 1642552) 8 (ELit 2147450880); KWord (SA (ELit 0) 1593592) 8 (ELit 1642560); KWord (SA (ELit 0) 1642560) 4 (ELit 1); KWr (SA (EVar 33) (-240)) (ELit 240); KAlign (EVar 33) 16; KRange (EVar 33) 35184372088832 140737488355328; KRange (EVar 35) 0 67108864]).
    { unfold know_ok.
      apply Forall_cons. { eapply kword_of_rw_cells with (k := 0%nat); [exact G1 | reflexivity | reflexivity | lia | reflexivity
                                  | apply Z.leb_le; reflexivity | apply Z.leb_le; reflexivity | reflexivity]. }
      apply Forall_cons. { eapply kword_of_rw_cells with (k := 0%nat); [exact G2 | reflexivity | reflexivity | lia | reflexivity
                                  | apply Z.leb_le; reflexivity | apply Z.leb_le; reflexivity | reflexivity]. }
      apply Forall_cons. { eapply kword_of_rw_cells with (k := 0%nat); [exact G3 | reflexivity | reflexivity | lia | reflexivity
                                  | apply Z.leb_le; reflexivity | apply Z.leb_le; reflexivity | reflexivity]. }
      apply Forall_cons. { eapply kword_of_rw_cells with (k := 0%nat); [exact G4 | reflexivity | reflexivity | lia | reflexivity
                                  | apply Z.leb_le; reflexivity | apply Z.leb_le; reflexivity | reflexivity]. }
      apply Forall_cons. { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite EP; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EP; evs; rewrite u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. split; [lia | rewrite EP; exact SP16]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R TOP_ENTRY m (seg_rom asegs) HR HK 120%nat [647932] (SCR [] [] []) 40%N.
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
    rreg HR' 12%bv L12.
    rreg HR' 21%bv L21.
    rreg HR' 27%bv L27.
    assert (L1' : getr R' 1 = Z_to_bv 64 TOP_SM_RET) by (rewrite L1; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L2' : getr R' 2 = Z_to_bv 64 S1) by (rewrite L2; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L8' : getr R' 8 = Z_to_bv 64 SP) by (rewrite L8; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L9' : getr R' 9 = Z_to_bv 64 S1) by (rewrite L9; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L10' : getr R' 10 = Z_to_bv 64 2752) by (rewrite L10; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L21' : getr R' 21 = Z_to_bv 64 0x7fff8000) by (rewrite L21; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (L27' : getr R' 27 = Z_to_bv 64 N) by (rewrite L27; h1_ar; first [reflexivity | f_equal; subst S1; Z.div_mod_to_equations; lia]).
    assert (MU1 : munch [(SP - 224, SP)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; h1_ar;
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; Z.div_mod_to_equations; lia|]).
      apply Forall_nil. }
    assert (RC1 : rw_cells asegs M1 (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { subst M1. repeat (lazymatch goal with |- rw_cells _ _ _ (_ :: _ :: _) =>
        apply rw_cells_cons8_c; [h1_rwc1 Hlf HR0 WW|] end). h1_rwc1 Hlf HR0 WW. }
    assert (RC2 : rw_cells asegs M1 (S1 + 88) [C8 (Z_to_bv 64 D)]) by (subst M1 S1; h1_rwc1 Hlf HR0 WW).
    eapply evt_of_msteps; [exact Hms|].
    rewrite mkst_MS, HRe, L1', L2', L8', L9', L10', L21', L27'.
    apply evt_done.
    do 15 eexists; split; [reflexivity|].
    split; [exact MU1|]. split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [subst M1; apply stk_mem_denot; exact ST|].
    split; [exact RC1 | exact RC2].
  Qed.
End TopH1.
