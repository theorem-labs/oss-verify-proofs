(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmGlue LbA_PmVops LbA_PmLH LbA_PmU2K LbA_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ARM_TABLE_A : list Z := [0xefb74; 0xf03c4; 0xf043c; 0xefbe8; 0xefbe8; 0xf00d8; 0xf033c; 0xf00e8; 0xefe0c; 0xf03fc; 0xefac0; 0xf067c; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xf0930; 0xf0930; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef260; 0xef260; 0xef260; 0xef260; 0xef260; 0xef260; 0xf0930; 0xefb74; 0xef260; 0xef260; 0xf00d8; 0xf0930; 0xefe0c; 0xefac0; 0xef244; 0xf0930; 0xef244; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xef260; 0xef244; 0xef244; 0xef244; 0xef244; 0xef260; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef244; 0xef260; 0xef260; 0xf0930; 0xf0930; 0xf0930; 0xef244; 0xef244; 0xef244; 0xef244; 0xf0930; 0xef260; 0xf0930; 0xef260; 0xef260; 0xef260; 0xef260; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xf0930; 0xef260; 0xef260; 0xef244; 0xf0930; 0xef244].

Definition arm_pcA (t : Z) : Z := if ((1 <=? t) && (t <=? 107))%bool then nth (Z.to_nat (t - 1)) ARM_TABLE_A 0xf0930 else 0xf0930.

Definition ARM_PCS_A : list Z := [0xef244; 0xef260; 0xefac0; 0xefb74; 0xefbe8; 0xefe0c; 0xf00d8; 0xf00e8; 0xf033c; 0xf03c4; 0xf03fc; 0xf043c; 0xf067c; 0xf0930].

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
      assert (HK : know_ok asegs (Eseed RR (wenv_vals w ++ [])) mm [KImg 0x24204 0x243b0])
        by (apply Forall_cons; [apply kimg_of_mem_inv; [exact (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | lia | lia] | apply Forall_nil]) end;
    lazymatch type of E10 with _ = Z_to_bv 64 (?tt - 1) =>
      pose proof (regs_tbl_cons w [] _ RT_ARM 10%bv (ELit (tt - 1)) E10 HT) as HTd end;
    pm_goR0 HHm (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) KR VIS RF HTd (@nil word) [KImg 0x24204 0x243b0] HK 12%nat ARM_PCS_A (@nil bool) 41%N RT_ARM;
    [ split_scs
    | let msF1 := fresh "msF" in let mo1 := fresh "mo" in let R1 := fresh "R" in
      intros msF1 mo1 R1 KR1 MP1 VIS1 RF1 MI1 HT1 HR1 Hlf1;
      eapply (K msF1 mo1 R1 KR1); [exact VIS1 | exact RF1 | eapply (pmxa_mpres H HHm LINV); [exact X | exact MP1]
        | intros r Hr; repeat (destruct Hr as [<-|Hr]; [first [exact (HR1 _) | (rewrite (HR1 _); symmetry; rtf HTd)] |]); destruct Hr ] ].

  Lemma pm_dispatchA : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (t : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xef228) fc None m (seg_rom asegs) -> rfull R ->
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
