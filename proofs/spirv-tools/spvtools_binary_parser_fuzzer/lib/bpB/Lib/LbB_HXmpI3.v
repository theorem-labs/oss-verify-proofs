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
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_HXmpS LbB_HEmpK LbB_HXmpD LbB_HXmpI LbB_HXmpI2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma land_1E : forall k, Z.land k 1 = k mod 2.
Proof. intros k. pose proof (Z.land_ones k 1 ltac:(lia)) as H. exact H. Qed.

Lemma bseq_pow2E : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ Z.land bc (bc - 1) = 0) \/ (3 <= bc < 2 ^ 31 /\ Z.land bc (bc - 1) <> 0).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia | left; split; [reflexivity | reflexivity] | right; split; [lia | vm_compute; discriminate] ] |]).
  destruct Hin.
Qed.

Lemma bseq_land_boundE : forall bc, In bc BSEQ -> 0 <= Z.land bc (bc + -1) < 2 ^ 31.
Proof.
  intros bc Hin. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ lazymatch goal with |- context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end; lia |]).
  destruct Hin.
Qed.

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
  [SE (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) 8 (EAlu ALU_ADD (EVar 32) (ELit 16));
   SE (SA (EVar 32) 16) 8 (EVar 33); SE (SA (EVar 33) 0) 8 (EVar 39)].

Definition KNF : list kentry :=
  [KWr (SA (EVar 33) 0) (ELit 8); KWr (SA (EVar 32) 16) (ELit 8);
   KWr (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 36)) (EVar 37)) 0) (ELit 8);
   KRange (EVar 32) 0x6e8000 (2 ^ 47 - 40); KRange (EVar 33) 0x6e8000 (2 ^ 47 - 24)].
Definition SCR_F0 := SCR [false; false; false; false; false; true; false; true] [EVar 37; EVar 38; EVar 39] [].
Definition SCR_F2 := SCR [false; false; false; false; false; true; false; false; false; false; false] [EVar 37; EVar 38; EVar 39; EVar 40] [].
Definition SCR_F3 := SCR [false; false; false; false; false; true; false; false; false; true; true; false] [EVar 37; EVar 38; EVar 39; EVar 40] [].
Definition SCR_F4 := SCR [false; false; false; false; false; true; false; false; false; true; false; false] [EVar 37; EVar 38; EVar 39; EVar 40] [].

Section EmpI3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation ISTATEx := (ISTATE H gp tp s11 spz obj key).

  Lemma front_j2 : forall (s : as_St H) (msF : machine_state) (mo : Model) (m M1 : mem) (F : bvmap 5 word) (fc : bv 32)
      (R R3 : bvmap 5 word) (errv' : word) (LB' LBm' : list block) (p bl2 bc2 fn k1 v1 : Z) (rest : list (Z * (Z * Z)))
      (rehashed : bool) (z1 z5 z6 z7 z8 z9 z12 z14 z15 z16 z17 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31 : word),
    as_VIS H s msF = MS R F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs) -> rfull R ->
    CatSim.msteps asegs (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 E_INS) m (seg_rom asegs))
                        (@PropExec.mkst (PropExec.mkFP F fc) R3 (Z_to_bv 64 E_J2) M1 (seg_rom asegs)) ->
    R3 = mkR z1 (Z_to_bv 64 (spz - 96)) gp tp z5 z6 z7 z8 z9 (Z_to_bv 64 p) (Z_to_bv 64 (hmod k1 bc2)) z12 (Z_to_bv 64 bl2)
             z14 z15 z16 z17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) z20 z21 z22 z23 z24 z25 (rShe (Z_to_bv 64 (obj + 24)))
             s11 z28 z29 z30 z31 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) ->
    IPREx s mo m errv' LB' LBm' p bl2 bc2 ((fn, (k1, v1)) :: rest) rehashed ->
    munch [(p, p + 8); (obj + 16, obj + 24); (bl2 + 8 * hmod key bc2, bl2 + 8 * hmod key bc2 + 8)] m M1 -> wmono asegs m M1 ->
    mem_grows m M1 -> stk asegs M1 lo spz ->
    rw_cells asegs M1 p [C8 (Z_to_bv 64 fn)] -> rw_cells asegs M1 (obj + 16) [C8 (Z_to_bv 64 p)] ->
    rw_cells asegs M1 (bl2 + 8 * hmod key bc2) [C8 (Z_to_bv 64 (obj + 16))] ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m M1 F fc R R3 errv' LB' LBm' p bl2 bc2 fn k1 v1 rest rehashed
      z1 z5 z6 z7 z8 z9 z12 z14 z15 z16 z17 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31
      VIS FHF Hms HRe FRZ KR IP MU1 WM1 MG1 ST1 Cn1 Cs1 Cb1.
    pose proof IP as IP0. destruct IP0 as (_ & _ & _ & _ & _ & _ & MI & _).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (front_tail H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s msF1 mo1 m M1 F fc); [exact VIS1 | exact FRZ | exact KR1 | | exact MU1 | exact WM1 | exact MG1 | exact MI1 | exact ST1
                                    | exact Cn1 | exact Cs1 | exact Cb1].
    destruct IP as (MPx & IPr). split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact IPr].
  Qed.

End EmpI3.
