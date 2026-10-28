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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmGlue LbB_PmVops LbB_PmLH LbB_PmU2K LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ARM_TABLE_A : list Z := [0xf1f1c; 0xf26e0; 0xf2744; 0xf1fa0; 0xf1fa0; 0xf23f4; 0xf2628; 0xf2404; 0xf2190; 0xf26fc; 0xf1e48; 0xf2950; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf2bf8; 0xf2bf8; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14cc; 0xf14cc; 0xf14cc; 0xf14cc; 0xf14cc; 0xf14cc; 0xf2bf8; 0xf1f1c; 0xf14cc; 0xf14cc; 0xf23f4; 0xf2bf8; 0xf2190; 0xf1e48; 0xf14b0; 0xf2bf8; 0xf14b0; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf14cc; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14cc; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14cc; 0xf14cc; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf14b0; 0xf14b0; 0xf14b0; 0xf14b0; 0xf2bf8; 0xf14cc; 0xf2bf8; 0xf14cc; 0xf14cc; 0xf14cc; 0xf14cc; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf2bf8; 0xf14cc; 0xf14cc; 0xf14b0; 0xf2bf8; 0xf14b0].

Definition arm_pcA (t : Z) : Z := if ((1 <=? t) && (t <=? 107))%bool then nth (Z.to_nat (t - 1)) ARM_TABLE_A 0xf2bf8 else 0xf2bf8.

Definition ARM_PCS_A : list Z := [0xf14b0; 0xf14cc; 0xf1e48; 0xf1f1c; 0xf1fa0; 0xf2190; 0xf23f4; 0xf2404; 0xf2628; 0xf26e0; 0xf26fc; 0xf2744; 0xf2950; 0xf2bf8].

Definition DISP_KEPT : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma In_range_enumA : forall t lo n, lo <= t < lo + Z.of_nat n -> In t (map (fun k => lo + Z.of_nat k) (seq 0 n)).
Proof. intros t lo n Ht. apply in_map_iff. exists (Z.to_nat (t - lo)). split; [lia|]. apply in_seq. lia. Qed.

Section OHD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Ltac disp1 w X KR VIS RF HT E10 K :=
    let HK := fresh "HK" in let HTd := fresh "HTd" in
    lazymatch type of VIS with _ = MS ?RR _ _ _ _ ?mm _ =>
      assert (HK : know_ok asegs (Eseed RR (wenv_vals w ++ [])) mm [KImg 0x23da4 0x23f50])
        by (apply Forall_cons; [apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | lia] | apply Forall_nil]) end;
    lazymatch type of E10 with _ = Z_to_bv 64 (?tt - 1) =>
      pose proof (regs_tbl_cons w [] _ RT_ARM 10%bv (ELit (tt - 1)) E10 HT) as HTd end;
    pm_goR0 HHm (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) KR VIS RF HTd (@nil word) [KImg 0x23da4 0x23f50] HK 12%nat ARM_PCS_A (@nil bool) 41%N RT_ARM;
    [ split_scs
    | let msF1 := fresh "msF" in let mo1 := fresh "mo" in let R1 := fresh "R" in
      intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1;
      eapply (K msF1 mo1 R1 KR1); [exact VIS1 | exact RF1 | eapply (pmxa_mpres H HHm LINV); [exact X | exact MP1]
        | intros r Hr; repeat (destruct Hr as [<-|Hr]; [first [exact (HR1 _) | (rewrite (HR1 _); symmetry; rtf HTd)] |]); destruct Hr ] ].

  Lemma pm_dispatchA : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (t : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf1494) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_ARM -> PropExec.getr R 10%bv = Z_to_bv 64 (t - 1) -> 1 <= t <= 107 ->
    (forall msF1 mo1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (arm_pcA t)) fc None m (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m mo1 c ins tbl ftbl TB spal ->
       (forall r, In r DISP_KEPT -> PropExec.getr R1 r = PropExec.getr R r) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc t Q OK X KR VIS RF HT E10 Ht K.
    pose proof (In_range_enumA t 1 107 ltac:(lia)) as HIn. vm_compute in HIn.
    repeat match type of HIn with
           | _ \/ _ => destruct HIn as [HIn|HIn]; [subst t; disp1 w X KR VIS RF HT E10 K |]
           | False => destruct HIn
           end.
  Qed.
End OHD.
