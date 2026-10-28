(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtD LbB_NtI LbB_NtI2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_HEmpI3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac sc_djX := cbn [sc_denot]; unfold flat, estart, elenZ; evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia;
  rewrite ?u64_of_Z by lia; cbn [a_off a_base]; lia.
Ltac sc_shdjX :=
  cbn [sc_denot]; unfold flat, elenZ;
  repeat (erewrite estart_sh; [| evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity | lia]);
  unfold estart; cbn [a_base a_off]; evs; rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z by lia; rewrite ?u64_of_Z by lia; cbn [edenot];
  repeat match goal with
  | |- context [?a / 8] =>
      let t := fresh "t" in let Ht := fresh "Ht" in
      pose proof (div8_bound a ltac:(lia)) as Ht; set (t := a / 8) in *; clearbody t
  end;
  rewrite ?u64_of_Z by lia;
  unfold SHBASE; lia.
Ltac sc_andE := cbn [sc_denot]; evs; rewrite w_addm by lia; rewrite w_and by lia; first [rewrite br_ne by lia | rewrite br_eq by lia]; bool_lia.

Ltac front_sc Hrd_b Hfl_b :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCDisj (SA (EAlu ALU_SRL _ _) _) _ _ _) => sc_shdjX
  | |- sc_denot _ _ _ (SCDisj _ _ (SA (EAlu ALU_SRL _ _) _) _) => sc_shdjX
  | |- sc_denot _ _ _ (SCDisj _ _ _ _) => sc_djX
  | |- sc_denot _ _ _ (SCBr _ _ (EAlu ALU_AND _ _) _) => sc_andE
  | |- sc_denot _ _ _ (SCReadBase (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _ _ _) => exact Hrd_b
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_ADD (EMd _ _ _) _) _) _) => exact Hfl_b
  | |- _ => try sc_auto1; try sc_shdj; try sc_dj
  end.

Definition LGF : list sentry :=
  [SE (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 (EAlu ALU_ADD (EVar 34) (ELit 16));
   SE (SA (EVar 34) 16) 8 (EVar 33); SE (SA (EVar 33) 0) 8 (EVar 39)].

Definition KNF : list kentry :=
  KNI ++ [KWr (SA (EVar 33) 0) (ELit 8); KWr (SA (EVar 34) 16) (ELit 8);
          KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8);
          KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 34) 0x6e8000 (2 ^ 47 - 40); KRange (EVar 33) 0x6e8000 (2 ^ 47 - 32)].
Definition SCR_F0 := SCR [true; true; true; true; true; true; true; true] [EVar 37; EVar 38; EVar 39] [].
Definition SCR_F2 := SCR [true; true; true; true; true; true; true; false; true; false; true] [EVar 37; EVar 38; EVar 39; EVar 40] [].
Definition SCR_F3 := SCR [true; true; true; true; true; true; true; false; true; true; true; true] [EVar 37; EVar 38; EVar 39; EVar 40] [].
Definition SCR_F4 := SCR [true; true; true; true; true; true; true; false; true; true; false; true] [EVar 37; EVar 38; EVar 39; EVar 40] [].

Section NtI3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H tp ty enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Lemma front_j2 : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M1 : mem) (F : bvmap 5 word) (fc : bv 32)
      (R R3 : bvmap 5 word) (errv' : word) (LB' LBm' : list block) (p bl2 bc2 fn k1 : Z) (v1 : Z * Z * Z) (rest : list ent)
      (rehashed : bool) (j584 : word) (z1 z5 z6 z7 z11 z13 z14 z16 z17 z18 z19 z21 z22 z25 z27 z28 z29 z31 : word),
    as_VIS H s msF = MS R F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs) -> rfull R ->
    CatSim.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 E_INS) m (seg_rom asegs))
                        (@PropExec.mkst (PropExec.mkFP F fc) R3 (Z_to_bv 64 E_J2) M1 (seg_rom asegs)) ->
    R3 = mkR z1 (Z_to_bv 64 S1) gp tp z5 z6 z7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 (hmod k1 bc2)) z11
             (Z_to_bv 64 bl2) z13 z14 (Z_to_bv 64 SHBASE) z16 z17 z18 z19 s4 z21 z22 (Z_to_bv 64 p) wd z25
             (Z_to_bv 64 (obj + 24)) z27 z28 z29 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) z31 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ((fn, (k1, v1)) :: rest) rehashed j584 ->
    munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * hmod key bc2, bl2 + 8 * hmod key bc2 + 8)] m M1 -> wmono asegs m M1 ->
    mem_grows m M1 -> stk asegs M1 lo (S1 + 672) ->
    rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)] -> rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    rw_cells asegs M1 (bl2 + 8 * hmod key bc2) [C8 (Z_to_bv 64 (obj + 16))] ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M1 F fc R R3 errv' LB' LBm' p bl2 bc2 fn k1 v1 rest rehashed j584
      z1 z5 z6 z7 z11 z13 z14 z16 z17 z18 z19 z21 z22 z25 z27 z28 z29 z31
      VIS FHF Hms HRe FRZ KR IP MU1 WM1 MG1 ST1 Cn1 Cs1 Cb1.
    pose proof IP as IP0. destruct IP0 as (_ & _ & _ & _ & _ & _ & _ & _ & MI & _).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (front_tail H HH gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0
              s msF1 mo1 m M1 F fc); [exact VIS1 | exact FRZ | exact KR1 | | exact MU1 | exact WM1 | exact MG1 | exact MI1 | exact ST1
                                    | exact Cn1 | exact Cs1 | exact Cb1].
    destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
  Qed.

End NtI3.
