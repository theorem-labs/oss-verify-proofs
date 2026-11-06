(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From Stdlib Require NArith PArith FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueZ.

(* [comment removed for export] *)
Module SecBump.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_geom"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "aa_sec"; "aa_frames"; "budget_bound"; "budget_ok_alloc"; "ageom"; "class_state"; "depot_state"; "mkAA"; "qbatch"; "sec_chunk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayCommit"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv"; "bumpV"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv.
Import ListNotations.
Open Scope Z_scope.

Definition bumpP (A : AA) : AA := ltac2:(tb__ "0|0|
S1dS10VA;A1ScVA;A1SbVA;A1S16VA;A1S22S13VA;A1S21A2S12VA;A1S15VA;A1S14VA;A1SdVA;A1SfVA;A1SeVA;A1S11VA;A1SaVA;A1S9VA;A1S8VA;A1Af").
Lemma bumpP_same : ltac2:(tb__ "0|3|
S7S1S0S1aS10S20R1A1M0A1S10R1A1A3S1S0S4S1bA1ScG0A1ScR1A1A3S1S0S5SbG0A1SbR1A1A3S1S0S4S1fA1S16G0A1S16R1A1A3S1S0S3S13G0A1S22S13R1A1S21A2A3S1S0S4S6S3S3A2A1M1S12G0A1S12R1A1A3S1S0S4S1eA1M2S15G0A1S15R1A1A3S1S0G2S14G0A1S14R1A1A3S1S0S1cSdG0A1SdR1A1A3S1S0S4S3A1SfG0A1SfR1A1A3S1S0S4G1A1SeG0A1SeR1A1A3S1S0S5S11G0A1S11R1A1A3S1S0G1S17G0A1S17R1A1A3S1S0S3SaG0A1SaR1A1A3S1S0S3S9G0A1S9R1A1A3S0S3S8G0A1S8R1A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2FA;").
Proof. intros A. repeat split; reflexivity. Qed.
Lemma bumpP_bumpV : ltac2:(tb__ "0|0|
S7S3S0S7S20S24R2R1A2A1S24S20R2A1R1A2A3Fn;FA;").
Proof. intros A n. reflexivity. Qed.
Lemma budget_boundD_bumpP : ltac2:(tb__ "0|0|
S7S0S3S23S20R1A1A1S22S23R1A1S21A2A3FA;").
Proof. intros A. unfold budget_boundD. cbn [aa_V aa_Km aa_Kf aa_ptr_committed aa_depot bumpP]. lia. Qed.
Lemma budget_bound_bumpP : ltac2:(tb__ "0|0|
S7S0S3S18S20R1A1A1S18R1A1A3FA;").
Proof. intros A. reflexivity. Qed.
Lemma budget_ok_alloc_bumpP : ltac2:(tb__ "0|0|
S7S3S2S19S20R2A1R1A2S19R2R1A2A2Fn;FA;").
Proof. intros A n. unfold budget_ok_alloc. cbn [aa_V aa_Km aa_Kf bumpP]. tauto. Qed.
End SecBump.

(* [comment removed for export] *)
Module SpineMallocS12iW2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "prod"; "pair"; "Some"; "nil"; "option"; "cons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "ss_next"; "swf"; "SVar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "creg_a"; "C1g"; "E2a"; "creg_b"; "F_gen"; "V_CLS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "E2a'"; "only_var"; "tab_ok"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "ClassID"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "d_k"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma WC1_2 : ltac2:(tb__ "0|0|
S2S5S11S4S14S1U2A1S0Z4A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma DC1_2 : ltac2:(tb__ "0|5|
S25S3S22Z0R1A2S22R1Z7A2A2S2ScS8S7S8SeSeA2A1M0S7SfA1M1A2M2A1S20S4S27S1U2A1M3S0Z4M4R2A4A1S4S14G3S0G4A3A1A2SaG2S9G0G1S28R2A1S17A4A2A3F_;Fk;").
Proof.
  intros k Hk. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
Qed.

Lemma OVa_2 : ltac2:(tb__ "0|0|
S2S5S1aP9dS13S1U2A1S0Z4A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OVb_2 : ltac2:(tb__ "0|0|
S2S5S1aP9dS16S1U2A1S0Z4A3A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABa_2 : ltac2:(tb__ "0|0|
S2S5S1bP9dS13S1U2A1S0Z4A3S21Z208S23S24S1cS1dS1eS1cS1fA1A1A1A1A1A1A5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABb_2 : ltac2:(tb__ "0|0|
S2S5S1bP9dS16S1U2A1S0Z4A3S21Z18U3eA5S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXa_2 : ltac2:(tb__ "0|2|
S2S26S10S4S19U2M0S0Z4M1A3A1A1S10S4S15S1G0A1S0G1A3A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Da'_2 : ltac2:(tb__ "0|7|
S2ScS8S7S8SeSeA2M0A1M1S7SfA1M2A2M3A1S20S4S15S1U2M4A1M5S0Z4M6A3A1S4S19G4S0G6A3A1A2SaG3S9G1G2SdG0S9SeSeS13G5S0G6A3S12S18A1A4SbG0A1A3SbSfA1A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wa'_2 : ltac2:(tb__ "0|0|
S2S5S11S4S19U2S0Z4A3A1A1S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SpineMallocS12iW2.

(* [comment removed for export] *)
Module SpineCallocS1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "rw"; "SVar"; "eval"; "swf"; "SLit"; "holds"; "sprop_below"; "sstate"; "sv_eqb"; "agree_below"; "rm"; "ss_facts"; "@Corelib.Init.Datatypes"; "prod"; "list"; "cons"; "bool"; "true"; "nil"; "pair"; "option"; "Some"; "app"; "fst"; "snd"; "andb"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "s_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "E_s1"; "P0c"; "F_hi_p"; "F_lo_p"; "prodc"; "s1_exits"; "stop_le"; "stop_pc"; "E_pre"; "neededp"; "s1_cuts"; "s1_cuts_pcs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "C1g"; "F_gen"; "V_ND"; "V_RZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "Pre_callocI"; "Kc_ok"; "last_link"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI"; "Jc"; "FACTSe"; "F_hi_e"; "F_lo_e"; "P0e"; "sa_c"; "nwc"; "sb_c"; "@Corelib.Init.Specif"; "sumbool"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "neededx"; "rzf_rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "rhoM_of"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1.SPINE1C"; "d_k"; "dp_okb"; "dp_pairs"; "@Stdlib.ZArith.ZArith_dec"; "Z_lt_dec"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation U := bv_unsigned.

Notation JG := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1.JG.
Notation rz_fam := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1.rz_fam.
Notation needed8_fam := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1.needed8_fam.
Notation needed8_0 := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1.needed8_0.
Notation needed8_bounds := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1.needed8_bounds.

Section SPINE1C.
Let segs : list Segment := segsA.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S49VAInv;VW;Vst;VA;VKc;S4PcA1A6").
Hypothesis law_die : ltac2:(tb__ "0|0|
S3fS1S10S2cQ40A1A1S60VAInv;R4R3R2R1A4S62S64Vsegs;SdR4A1A2S63Z182f1cU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Variable nW : nat.
Variable st : ustop.
Variable tmax : Z.
Let W : list ulink := Wcan nW.

Definition d_k (k : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S11SfS0S0A2M0S15S0S0S5cVk;A1S4S42A1A4M1S11G0G1S11G0S15S0S0S7S5dVk;A1A1S4S43A1A4S14G0A1A3A3A3").
Hypothesis WC1 : ltac2:(tb__ "0|0|
S1dS12S6S28S40VW;Vst;Vtmax;A3A1A1S13A3").
Hypothesis DC1 : ltac2:(tb__ "0|3|
S2dS1eS24Z0R1A2S24R1Z7A2A2S1dS16SfS10SfS0S0A2A1M0S10S2A1M1A2M2A1S4aS28S33VW;Vst;Vtmax;R2A4A1S28S40VW;Vst;Vtmax;A3A1A2S17G2S15G0G1S65R2A1S41A4A2A3F_;Fk;").

Lemma e_s1_c1g : ltac2:(tb__ "0|0|
S2dS3fS44S1S10S2cQ40A1A1S2fS1S1eS24Z0R7A2S24R7Z7A2A2S21Vsegs;S23VW;Vst;R7R6R5A5S33VW;Vst;Vtmax;R8A4R2R4R3A6S21Vsegs;S23VW;Vst;R8R7R6A5S40VW;Vst;Vtmax;A3R3R5R4A6F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fk;").
Proof.
  intros k A Kc rho tp w rhoE Hk H.
  pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.

  set (nv := bv_unsigned (rw rho 12%positive)).
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E150 : rw rhoE 150%positive = Z_to_bv 64 (rz nv)). { rewrite <- (Hagw 150%positive) by (unfold GW; lia). reflexivity. }

  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HF : Forall (holds rhoE) (F_fam tmax k)).
  { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S E_s1]. apply in_or_app. right. exact Hp. }
  unfold F_fam in HF. pose proof (Forall_inv HF) as F1. pose proof (Forall_inv (Forall_inv_tail HF)) as F2.
  cbn [holds eval] in F1, F2. rewrite E12 in F1, F2. fold nv in F1, F2.
  assert (KB : 0 <= rzf_lo k <= 64513 /\ 0 <= rzf_hi k <= 64513 /\ 16 <= rzf_rz k <= 1024 /\ rzf_rz k mod 16 = 0).
  { assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn; lia. }
  destruct KB as (Rlo & Rhi & RZB1 & RZB2).
  rewrite u64_lit in F1 by lia. rewrite u64_lit in F2 by lia.
  pose proof (needed8_bounds k nv Hk (conj F1 F2)) as (NB & NA & NR). pose proof (rz_fam k nv Hk (conj F1 F2)) as RZ.
  assert (Hnv64 : nv <= 64512) by lia.
  change (C1g W st tmax) with (ax_setS (E_s1 W st tmax k) (ax_S (C1g W st tmax))).
  eapply SPA_restate; [exact WC1 | exact (DC1 k Hk) | reflexivity | | | exact H].
  -
    assert (EN : eval rhoE (neededx k) = Z_to_bv 64 (needed8 nv)).
    { unfold neededx. destruct (Z.eq_dec k 0) as [->|Hk0].
      - cbn [Z.eqb eval]. rewrite needed8_0 by (cbn in F1, F2; lia). reflexivity.
      - replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (k =? 8) with false by (symmetry; apply Z.eqb_neq; lia).
        unfold rup8. cbn [eval]. rewrite E12. apply bv_eq. rewrite add_val, and_val, add_val, !u64_lit by lia. fold nv.
        rewrite (Z.mod_small (nv + 7)) by lia. rewrite (needed8_fam k nv) by lia.
        change 18446744073709551608 with (2 ^ 64 - 2 ^ 3). rewrite land_high_mask by lia.
        pose proof (Z.mod_pos_bound (nv + 7) (2 ^ 3) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
    unfold diffs_ok, d_k, V_ND, V_RZ.
    apply Forall_cons; [cbn [fst snd]; rewrite EN; cbn [eval]; rewrite E157; reflexivity|].
    apply Forall_cons; [cbn [fst snd]; rewrite EN; cbn [eval]; rewrite E157; reflexivity|].
    apply Forall_cons; [cbn [fst snd eval]; rewrite E150, RZ; reflexivity|]. apply Forall_nil.
  -
    unfold F_gen, V_RZ, V_ND. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E150, ?E157, ?E12, ?RZ; fold nv;
      rewrite ?u64_lit by lia; try lia.
    + rewrite add_val, !u64_lit by lia. fold nv. rewrite Z.mod_small by lia. lia.
Qed.

Definition dp_pairs (k : Z) : list (sv * sv) := ltac2:(tb__ "0|1|
S11SfS0S0A2M0S15S0S0S37S4PcA1A4S11G0S15S0S0S3cVk;A1S5cVk;A1A4S14G0A1A3A3").
Definition dp_okb (k : Z) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S4cSfS0S0A2M0G0S4dG0G0S1bSbS19S0S0R2A3S19S0S0R1A3A2SbS1aS0S0R2A3S1aS0S0R1A3A2A2Lq;S67Vk;A1A3Lp;Vd;A3").
Hypothesis WE1 : ltac2:(tb__ "0|0|
S2dS1eS24Z0R1A2S24R1Z8A2A2S1dS12S6S28S33VW;Vst;Vtmax;R2A4A1A1S13A3F_;Fk;").
Hypothesis DE1 : ltac2:(tb__ "0|3|
S2dS1eS24Z0R1A2S24R1Z8A2A2S1dS12S16SfS10SfS0S0A2A1M0S10S2A1M1A2M2A1S12Lx;S4aS28S3bVW;Vst;Vtmax;R2A4A1S28S33VW;Vst;Vtmax;R2A4A1A2G2G2S12Lp;R1G0G1S66R5R2A2Ll;Ld;Xfx1Lp;S1cX16x2S13A3F_;Fk;").

Lemma state_diff_nf_incl : ltac2:(tb__ "0|3|
SaSaS10SfS0S0A2A1M0S10S2A1M1S1dS16SfG0G1A2M2A1S4aR4R3A2S17G2S15G0G1R2R1A4A2A3S4eS2R2SeR4A1A3F_;Fnf;Fd;FS';FS;").
Proof.
  intros S S' d nf H. unfold state_diff in H. destruct (ss_pc S =? ss_pc S'); [|discriminate].
  destruct (sfcsr_diff _ _); [|discriminate]. destruct (osv_diff _ _); [|discriminate].
  destruct (svs_diff (ss_regs S) _); [|discriminate]. destruct (svs_diff (ss_fregs S) _); [|discriminate].
  destruct (objs_diff _ _); [|discriminate]. injection H as _ <-. intros p Hp. apply filter_In in Hp. exact (proj1 Hp).
Qed.

Lemma e_pre_s1 : ltac2:(tb__ "0|1|
S2dS3fS44S1S10S2cQ40A1M0A1S2fS1S1eS24Z0R7A2S24R7Z8A2A2S1dG0S5R2S37A2S3R2PcA2A3S21Vsegs;S23VW;Vst;R8R7R6A5S3bVW;Vst;Vtmax;R9A4R3R5R4A6S21Vsegs;S23VW;Vst;R9R8R7A5S33VW;Vst;Vtmax;RaA4R4R6R5A6F_;F_;F_;FrhoE;Fw;Ftp;Frho;FKc;FA;Fk;").
Proof.
  intros k A Kc rho tp w rhoE Hk EP H.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (DE1 k Hk) as HD. destruct (state_diff _ _) as [[d nf]|] eqn:ED; [|discriminate HD].
  change (E_s1 W st tmax k) with (ax_setS (E_pre W st tmax k) (ax_S (E_s1 W st tmax k))).
  eapply SPA_restate; [exact (WE1 k Hk) | exact ED | reflexivity | | | exact H].
  -
    unfold diffs_ok. apply Forall_forall. intros p Hp.
    pose proof (proj1 (forallb_forall _ _) HD p Hp) as Hq. apply existsb_exists in Hq. destruct Hq as (q & Hq & Hpq).
    apply andb_prop in Hpq. destruct Hpq as [E1 E2]. apply sv_eqb_sound in E1, E2. rewrite E1, E2.
    unfold dp_pairs in Hq. destruct Hq as [<-|[<-|[]]]; cbn [fst snd].
    + exact EP.
    + unfold neededp, neededx. destruct (k =? 0); [reflexivity|]. unfold rup8p, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1.rup8.
      destruct (k =? 8); cbn [eval]; cbn [eval] in EP; rewrite EP; reflexivity.
  -
    apply Forall_forall. intros p Hp. apply (state_diff_nf_incl _ _ _ _ ED) in Hp. cbn [ss_facts ax_S E_s1] in Hp.
    apply in_app_or in Hp. destruct Hp as [Hp|Hp].
    + apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S E_pre]. apply in_or_app. left. apply in_or_app. left. exact Hp.
    + assert (HP : Forall (holds rhoE) (F_fam_p tmax k)).
      { apply Forall_forall. intros q Hq. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S E_pre]. apply in_or_app. right. exact Hq. }
      unfold F_fam_p in HP. unfold F_fam in Hp.
      pose proof (Forall_inv HP) as P1. pose proof (Forall_inv (Forall_inv_tail HP)) as P2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HP))) as P3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HP)))) as P4.
      cbn [holds] in P1, P2. rewrite EP in P1, P2.
      destruct Hp as [<-|[<-|[<-|[<-|[]]]]]; [exact P1 | exact P2 | exact P3 | exact P4].
Qed.

Lemma rc_prod : ltac2:(tb__ "0|0|
S3fS1S1ScS4fS5fR3S31R2A1A2R1A3S1dS2cQ40A1S5R2S37A2S3R2PcA2A3F_;FrhoE;Frho;FA;").
Proof.
  intros A rho rhoE (Hw & _ & _). unfold prodc, V_C, V_S. cbn [eval].
  rewrite <- (Hw 143%positive) by (unfold GW; lia). rewrite <- (Hw 144%positive) by (unfold GW; lia). rewrite <- (Hw 12%positive) by (unfold GW; lia).
  rewrite rc_12, rc_143, rc_144. unfold nwc, calloc_size. cbn [eval]. apply mul_word_comm.
Qed.

Lemma s1c_exits : ltac2:(tb__ "0|0|
S2fOF_;S3fS44S1S10S2cQ40A1A1S30S30S1S2eVsegs;R8S21Vsegs;S23VW;Vst;R7R6S31R5A1A5S40VW;Vst;Vtmax;A3R1R4A5R3A4FrhoE;S1S2eVsegs;R9S21Vsegs;S23VW;Vst;R8R7S31R6A1A5S33VW;Vst;Vtmax;Z8A4R1R5A5R4A4FrhoE;S29S1S4bS29R2S38VnW;Vst;Vtmax;A3A3S2eVsegs;RcS21Vsegs;S23VW;Vst;RbRaS31R9A1A5R3R2R8A5S2fS20R7R1A1R8R1A1A2Lw';A4F_;FrhoE;FE;F_;F_;FR;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q R HC1 HSEC E rhoE HinE. unfold s1_exits in HinE. cbn [map] in HinE.
  assert (RS : forall k w, 0 <= k <= 8 -> SPA segs (JG W st A Kc (rho_c rho)) (E_pre W st tmax k) rhoE tp w ->
                            SPA segs (JG W st A Kc (rho_c rho)) (E_s1 W st tmax k) rhoE tp w).
  { intros k w Hk Hw. apply (e_pre_s1 k A Kc (rho_c rho) tp w rhoE Hk); [|exact Hw].
    destruct Hw as [_ [Hag _]]. exact (rc_prod A rho rhoE Hag). }
  destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]].
  9: { eapply triple_conseq; [intros w Hw; apply (RS 8 w ltac:(lia) Hw) | intros w Hw; right; exact Hw | apply HSEC]. }
  all: eapply triple_conseq; [intros w Hw; eapply (e_s1_c1g _ A Kc (rho_c rho) tp w rhoE); [|apply RS; [|exact Hw]]; lia | intros w Hw; right; exact Hw | apply HC1].
Qed.

Section FRONT.
Hypothesis HSW : stopJ_sw W st.
Hypothesis HUS : stopJ_stable W st.
Hypothesis Wa : ltac2:(tb__ "0|0|
S1dS12S6S55VW;Vst;A2A1S13A3").
Hypothesis Da : ltac2:(tb__ "0|4|
S1dS16SfS10SfS0S0A2M0A1M1S10S2A1M2A2M3A1S4aS28S46S45VW;Vst;A3A1S55VW;Vst;A2A2S17G3S15G1G2S11G0S15S0S0S4P18A1S7S61A1A4S14G0A1A3S14S2A1A4A2A3").
Hypothesis Wb : ltac2:(tb__ "0|0|
S1dS12S6S57VW;Vst;A2A1S13A3").
Hypothesis Fbh : ltac2:(tb__ "0|0|
S1dS12S4cS2S9S5bA1S18S2S51VW;Vst;A2S52A3A3S13A3").
Hypothesis Fbl : ltac2:(tb__ "0|0|
S1dS12S4cS2S9S5bA1S18S2S51VW;Vst;A2S53A3A3S13A3").
Hypothesis ENTh : ltac2:(tb__ "0|0|
S1dS12S2aS54VW;Vst;S52A3S34VW;Vst;S35A3S32A3S13A3").
Hypothesis ENTl : ltac2:(tb__ "0|0|
S1dS12S2aS54VW;Vst;S53A3S34VW;Vst;S36A3S32A3S13A3").

Lemma c_front : ltac2:(tb__ "0|5|
S3fS44S1S10S2cQ40M0A1A1S2fS25S26S2bG0S3R3PcA2A2S2bG0S3R3PdA2A2A2S27Z2Z40A2A2S21Vsegs;S50VW;Vst;R6R5A4S46S45VW;Vst;A3R4R3R2A6S21Vsegs;VJ;VW;Vst;R7R6A4S34VW;Vst;S58S25S2bG0S56R5A1A2M1Zfc01M2A2M3S1fG3A1M4A2S10S2A1L_;S68G1G2A2G3S36L_;G4S35L_;X58x2A3S5fR7S31R5A1A2R4R3A6F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w Hmul Hw.
  pose proof (c_instantiate_e law_die W st A Kc rho tp w HUS Wa Da Wb Fbh Fbl Hmul Hw) as H1.
  destruct (Z_lt_dec (bv_unsigned (nwc rho)) 64513).
  - exact (c_switch W st A Kc rho tp w F_lo_e F_lo_p HSW HUS ENTl H1).
  - exact (c_switch W st A Kc rho tp w F_hi_e F_hi_p HSW HUS ENTh H1).
Qed.

Section LE.
Hypothesis Cert1 : ltac2:(tb__ "0|0|
S1dS12S5aS5eUfa0S11S2dZ40a18S14S2dA1A3S4fS3dVnW;Vst;A2S38VnW;Vst;Vtmax;A3A6S13A3").

Theorem spine_s1c : ltac2:(tb__ "0|1|
S2fOF_;S3fS44S1S10S2cQ40M0A1A1S30S47R4A1S22Vsegs;R7VJ;VW;Vst;R6R5A4A3S25S26S2bG0S3R5PcA2A2S2bG0S3R5PdA2A2A2S27Z2Z40A2A2S1S2eVsegs;RaS21Vsegs;S23VW;Vst;R9R8S31R7A1A5S40VW;Vst;Vtmax;A3R1R6A5R5A4FrhoE;S1S2eVsegs;RbS21Vsegs;S23VW;Vst;RaR9S31R8A1A5S33VW;Vst;Vtmax;Z8A4R1R7A5R6A4FrhoE;S2eVsegs;RbS21Vsegs;S50VW;Vst;RaR9A4S46S45VW;Vst;A3R8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HKc Hokf Hmul HC1 HSEC.
  eapply triple_conseq; [intros w Hw; exact (c_front A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (P0 := P0c W st (if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p)).
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs _ GW P0 (rhoM_of A (rho_c rho)) tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs 4000%nat [0x40a18] GW (s1_cuts nW st) (s1_exits nW st tmax) (JG W st A Kc (rho_c rho)) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert1.
  - intros E rhoE HinE. exact (s1c_exits ok A Kc rho tp Q _ HC1 HSEC E rhoE HinE).
  - unfold s1_cuts, P0. destruct (Z_lt_dec _ _); [right; left; reflexivity | left; reflexivity].
Qed.
End LE.

Section PC.

Hypothesis Cert1pc : ltac2:(tb__ "0|0|
S1dS12S5aS5eUfa0S11S2dZ40a18S14S2dA1A3S4fS3eVnW;Vst;A2S38VnW;Vst;Vtmax;A3A6S13A3").
Hypothesis Est : st = UStopLeOrPc.
Hypothesis WPC : ltac2:(tb__ "0|2|
S10S2A1M0G0S4bG0R2S11G0S35S11G0S36S14G0A1M1A3A3A3S4bG0R2S11G0S3aVW;A1S11G0S39VW;A1G1A3A3A3S1dS12S6S28S34VW;Vst;S18S2R4R3A3A3A1A1S13A3F_;F_;Fsx;Ffx;").
Hypothesis DPC : ltac2:(tb__ "0|5|
S10S2A1M0G0S4bG0R2S11G0S35S11G0S36S14G0A1M1A3A3A3S4bG0R2S11G0S3aVW;A1S11G0S39VW;A1G1A3A3A3S1dS16SfS10SfS0S0A2M2A1M3G0A2M4A1S4aS28S34VW;Vst;R4A3A1S28S34VW;Vst;S18S2R4R3A3A3A1A2S17G4S15G3G0S14G2A1R3A4A2A3F_;F_;Fsx;Ffx;").
Hypothesis HWne : W <> [].

Lemma stop_pc_holds : ltac2:(tb__ "0|1|
S1SfSfS0S0A2M0S0A2OLx;S48S4P1cA1VW;A2G0S0G0OLp;R2S0S0S25S2bQ40S5R5R3A2A2Z1000A2Lnbp;Lbp;Xfx1Lpc;Lp;Xfx1S59S2S8R2A1S3aVW;A1A3F_;Frho;").
Proof.
  intros rho H. unfold stop_pc. destruct (last_link (SVar 28) W) as [[bp nbp] pc]. constructor; [|constructor].
  cbn [holds eval branch_taken]. unfold bv_ltu. rewrite u64_lit by lia. destruct (Z.ltb_spec (bv_unsigned (eval rho pc)) 4096); cbn; [discriminate | lia].
Qed.
Lemma stop_le_holds : ltac2:(tb__ "0|2|
S1SfSfS0S0A2M0S0A2OLx;S48S4P1cA1VW;A2G0S0G0OLp;R2S0S0S24S2bQ40M1S5R5R1A2A2S2bG1S5R5R2A2A2A2Lnbp;Lbp;Xfx1Lpc;Lp;Xfx1S59S2S8R2A1S39VW;A1A3F_;Frho;").
Proof.
  intros rho H. unfold stop_le. destruct (last_link (SVar 28) W) as [[bp nbp] pc]. constructor; [|constructor]. exact H.
Qed.

Theorem spine_s1c_pc : ltac2:(tb__ "0|1|
S2fOF_;S3fS44S1S10S2cQ40M0A1A1S30S47R4A1S22Vsegs;R7VJ;VW;Vst;R6R5A4A3S25S26S2bG0S3R5PcA2A2S2bG0S3R5PdA2A2A2S27Z2Z40A2A2S1S2eVsegs;RaS21Vsegs;S23VW;Vst;R9R8S31R7A1A5S40VW;Vst;Vtmax;A3R1R6A5R5A4FrhoE;S1S2eVsegs;RbS21Vsegs;S23VW;Vst;RaR9S31R8A1A5S33VW;Vst;Vtmax;Z8A4R1R7A5R6A4FrhoE;S2eVsegs;RbS21Vsegs;S50VW;Vst;RaR9A4S46S45VW;Vst;A3R8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Q HKc Hokf Hmul HC1 HSEC.
  eapply triple_conseq; [intros w Hw; exact (c_front A Kc rho tp w Hmul Hw) | intros w Hw; exact Hw |].
  set (fx := if Z_lt_dec (bv_unsigned (nwc rho)) 64513 then F_lo_p else F_hi_p).
  assert (Hfx : In fx [F_hi_p; F_lo_p]) by (unfold fx; destruct (Z_lt_dec _ _); cbn; tauto).

  apply (triple_pre_pure segs ok _ _ (unwind_stopJ W st (rhoM_of A (rho_c rho)))).
  { intros w [_ HJ]. exact (proj1 (proj2 (proj2 (proj2 HJ)))). }
  intros HST.
  assert (HSX : exists sx, In sx [stop_pc W; stop_le W] /\ Forall (holds (rhoM_of A (rho_c rho))) sx).
  { unfold unwind_stopJ in HST. rewrite Est in HST. destruct W as [|l W'] eqn:EW; [contradiction HWne; reflexivity|]. rewrite <- EW in *.
    destruct (last_link (SVar 28) W) as [[bp nbp] pc] eqn:EL. destruct HST as [Hp|Hl].
    - exists (stop_pc W). split; [left; reflexivity|]. apply stop_pc_holds. rewrite EL. exact Hp.
    - exists (stop_le W). split; [right; left; reflexivity|]. apply stop_le_holds. rewrite EL. exact Hl. }
  destruct HSX as (sx & Hsx & Hholds).
  set (P0 := P0c W st (fx ++ sx)).
  apply triple_conseq with (P := SPA segs (JG W st A Kc (rho_c rho)) P0 (rhoM_of A (rho_c rho)) tp) (Q := Q); [intros w Hw | intros w Hw; exact Hw |].
  { apply (SPA_withG_intro segs (J W st A Kc) GW P0 (rhoM_of A (rho_c rho)) tp w).
    change P0 with (ax_setS (P0c W st fx) (ax_S (P0c W st (fx ++ sx)))).
    eapply SPA_restate; [exact (WPC fx sx Hfx Hsx) | exact (DPC fx sx Hfx Hsx) | reflexivity | constructor | exact Hholds | exact Hw]. }
  apply (cfg_soundA segs 4000%nat [0x40a18] GW (s1_cuts_pcs nW st) (s1_exits nW st tmax) (JG W st A Kc (rho_c rho)) ok Q tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hokf; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | apply JM_stableA; [exact HUS | exact HKc]].
  - exact Cert1pc.
  - intros E rhoE HinE. exact (s1c_exits ok A Kc rho tp Q _ HC1 HSEC E rhoE HinE).
  - unfold s1_cuts_pcs, P0. fold W. unfold fx in *. clear - Hfx Hsx.
    destruct Hsx as [<-|[<-|[]]]; destruct (Z_lt_dec _ _); cbn; tauto.
Qed.
End PC.
End FRONT.
End SPINE1C.

Lemma stopJ_stable_1pc : stopJ_stable (Wcan 1) UStopLeOrPc.
Proof.
  intros rho rho' (Hw & _ & _) H. unfold unwind_stopJ, Wcan, Wcan_from, last_link, link_var in *. cbn [nth eval] in *.
  rewrite <- !Hw by (unfold NF; first [lia | discriminate]). exact H.
Qed.
End SpineCallocS1.

(* [comment removed for export] *)
Module CallocPosts.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "sprop"; "SVar"; "valuation"; "sobj"; "eval"; "FcsrFrm0"; "SLit"; "mkSS"; "DZero"; "SAlu"; "SPUle"; "ss_next"; "swf"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "list"; "prod"; "app"; "bool"; "true"; "None"; "false"; "nat"; "Some"; "option"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "cut_regs"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "V_RES"; "mkA"; "A_globals"; "KcA"; "ae_ret_calloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "F_res_facts"; "JL_malloc_null"; "JL_malloc_ok"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "block_obj"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PRODs"; "Lconv_S"; "s_fin"; "F_topr"; "Lc_null"; "Lc_ok"; "Lc_ok_S"; "NLC"; "Lconv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2"; "rho_c"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.POSTS"; "JLc_null"; "JLc_ok"; "PFc"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "mul"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation U := bv_unsigned.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition NLC : positive := 150%positive.
Definition PRODs : sv := SMd M_MUL (SVar 143) (SVar 144).
Definition s_fin : wsub := ltac2:(tb__ "0|1|
SfS13S46S0A2M0S10S46S0PcS3P8fA1A4SfG0S10S46S0PdS3P90A1A4S11G0A1A3A3").

Definition Lc_null (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S24S9S27S22A1S21S1fS1eA1SfS13S19S0A2M0S10S19S0UaS8Z0A1A4S11G0A1A3A2S20S7S17S0A1SfS5S2aS14S5S2cVW;A1S25A3A3S14S2S2bVW;Vst;A2S29S28A1A3S42S18A9S11S13S0S0A2A1A2").
Definition Lc_ok_S (W : list ulink) (st : ustop) (size : sv) (extra : list sprop) : sstate := ltac2:(tb__ "0|0|
S9S27S22A1S1fS1eA1S20S7S17S0A1SfS5S2aS14S5S2cVW;A1S14S5SfS5S33Vsize;SaA2S11S5A1A3S25A3A3A3S14S2Vextra;S14S2S2dS3PcA1A1S14S2S2bVW;Vst;A2S29S28A1A3A3A3S42S18A9").
Definition Lc_ok (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|2|
S24S41VW;Vst;S3PcA1M0S11S2A1A4SfS13S0S0A2M1S10S0S0S3S23A1G0A4S11G1A1A3A2").

Definition F_topr : sprop := ltac2:(tb__ "0|0|
ScSbS50S3S23A1S3bA3S8Z7fffff800000A1A2").
Definition Lconv_S (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|0|
S41VW;Vst;S3bSfS2S3eS11S2A1A3A4").
Definition Lconv (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S24S3cVW;Vst;A2SfS13S0S0A2M0S10S0S0S3S23A1S3bA4S11G0A1A3A2").

Section POSTS.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Definition JLc_null (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S4S12S34Q40A1M0A1M1S4G1S12S4aA1S49S1dS2eVAInv;VCST;VXGL;VA;VKc;R6R5R4R3R2R1AbS1dS1cG0S1R4P8fM2A2S1R6G2A2A3S1cG0S1R4P90M3A2S1R6G3A2A3A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition JLc_ok (A : AA) (Kc : KcA) : jpostA := ltac2:(tb__ "0|4|
S4S12S34Q40A1M0A1M1S4G1S12S4aA1S49S1dS2fVAInv;VCST;VXGL;VA;VKc;R6R5R4R3R2R1AbS1dS1cG0S1R4P8fM2A2S1R6G2A2A3S1cG0S1R4P90M3A2S1R6G3A2A3A2A2Lmd;Ltr;Ltp';Lrho';Ltp0;Lrho0;").
Definition PFc (W : list ulink) (st : ustop) : AA -> KcA -> list (axst * jpostA) := ltac2:(tb__ "0|1|
S4fS26SfS13S36S47A2M0S10S36S47S3fVW;Vst;A2S54R2R1A2A4SfG0S10S36S47S40VW;Vst;A2S55R2R1A2A4S11G0A1A3A3LKc;LA;").

Lemma SPA_x_restate1 : ltac2:(tb__ "0|3|
S4eS4S36S0S0S0S0S12S13S0S0A2M0A1M1S12S34Q40A1M2A1S4bS1cG1S39R8A1SfG0S10S0S0R7R6A4R3A3A3S1cG2S6RaR6A2S6RaR8A2A3S1cG2S6RbR6A2S6RbR8A2A3S1cS15S3aSdS37RbA1A1S10S0S0R8R7A4A2S16A3S4dS44ReRcRdR6R5A6S4dS44RfS53RdSfG0S10S0S0RaR9A4R8A3A2ReR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;FX;Fl';Fb';Fl;Fb;FA;Frho;FJ;").
Proof.
  intros J rho A b l b' l' X tp w EX Eb El HB [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [exact Hsm|]. split; [exact HMI|]. split.
  - unfold axwf in Hwf |- *. cbn. rewrite EX in Hwf. cbn [forallb] in Hwf. apply andb_prop in Hwf as [HX Hb]. apply andb_prop in HX as [_ HX].
    rewrite HB, HX, Hb. reflexivity.
  - split; [|exact Hhz]. unfold shadow_ok in Hsh |- *. cbn. rewrite EX in Hsh. constructor; [|exact (Forall_inv_tail Hsh)].
    pose proof (Forall_inv Hsh) as H1. unfold xr_ok in H1 |- *. cbn [fst snd] in H1 |- *. rewrite Eb, El. exact H1.
Qed.

Section CONV.
Variables (W : list ulink) (st : ustop).
Hypothesis Wcv : ltac2:(tb__ "0|0|
S1cS15SeS3cVW;Vst;A2A1S16A3").
Hypothesis Dcv : ltac2:(tb__ "0|4|
S1cS1bS13S12S13S0S0A2M0A1M1S12S2A1M2A2M3A1S51S37S40VW;Vst;A2A1S3cVW;Vst;A2A2S1aG3S10G1G2SfG0S10S0S0S3PcA1S3bA4S11G0A1A3SfS2S3eS11S2A1A3A4A2A3").
Hypothesis ENTcv : ltac2:(tb__ "0|0|
S1cS15S38S43VW;Vst;A2S31S22VW;Vst;A3S3dA3S16A3").
Hypothesis ENTnl : ltac2:(tb__ "0|0|
S1cS15S38S3fVW;Vst;A2S30S22VW;Vst;A3S3dA3S16A3").

Lemma fin_agree : ltac2:(tb__ "0|3|
S4S4S4cS1eS45R2A1R1A3S1cS34Q40A1M0S1R2P8fM1A2S1S45R3A1G1A2A3S1cG0S1R3P90M2A2S1S45R4A1G2A2A3S4cS1eR5S52R4S3dA2A3F_;F_;F_;Frho';Frho;").
Proof.
  intros rho rho' [Hw Hl] E143 E144. split.
  - intros i Hi. cbn [rho_sub rw]. unfold s_fin. cbn [wsub_get].
    destruct (Pos.eqb_spec i 12) as [->|N12]; [cbn [eval]; rewrite E143; unfold rho_c; rewrite !rw_set; reflexivity|].
    destruct (Pos.eqb_spec i 13) as [->|N13]; [cbn [eval]; rewrite E144; unfold rho_c; rewrite !rw_set; reflexivity|].
    cbn [eval]. rewrite <- (Hw i Hi). unfold rho_c. rewrite !rw_set. rewrite (proj2 (Pos.eqb_neq _ _) N12).
    replace (Pos.eqb i 143) with false by (symmetry; apply Pos.eqb_neq; unfold NF in Hi; lia).
    replace (Pos.eqb i 144) with false by (symmetry; apply Pos.eqb_neq; unfold NF in Hi; lia). reflexivity.
  - intros l. cbn [rho_sub rl]. rewrite <- (Hl l). reflexivity.
Qed.

Theorem calloc_conv : ltac2:(tb__ "0|1|
S4fS26S4S12S34Q40M0A1A1S4bS57S58S35G0S1R3PcA2A2S35G0S1R3PdA2A2A2S59Z2Z40A2A2S48S44S1eS45R4A1R3S56VW;Vst;R6R5A4R2A6S48S44S1eR5R4S32S22VAInv;VCST;VXGL;VW;Vst;R7R6A8R3A6F_;F_;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w Hmul (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  assert (E12c : rw (rho_c rho) 12%positive = nwc rho) by (unfold rho_c; rewrite !rw_set; reflexivity).
  assert (ENV : U (rw (rho_c rho) 12%positive) = U (rw rho 12%positive) * U (rw rho 13%positive)).
  { rewrite E12c. unfold nwc. rewrite calloc_size_val. exact (mul_exact _ _ Hmul). }
  assert (Erm : rm (rho_c rho) = rm rho) by reflexivity.
  unfold PFc in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
  -
    destruct HJL as (HJ & E143 & E144).
    exists (L_calloc_null AE_A W st), (JL_calloc_null AInv CST XGL A Kc), (rho_sub rho' s_fin), tp'.
    split; [left; reflexivity|]. split; [exact (fin_agree rho rho' Hag E143 E144)|].
    split; [exact (smatchA_entails segs _ _ s_fin rho' tp' w ENTnl Hsm)|].
    unfold JL_calloc_null. unfold JL_malloc_null in HJ. destruct HJ as (A' & HA' & H1 & H2 & HV & H4 & H5 & H6 & HM & HK & HC).
    exists A'. rewrite ENV in HV, HC. rewrite Erm in HM.
    split; [unfold AInv, AInvA in *; rewrite (rm_rho_sub' rho' s_fin); exact HA'|].
    rewrite (rm_rho_sub' rho' s_fin). repeat (split; [assumption|]). exact HC.
  -
    destruct HJL as (HJ & E143 & E144).
    assert (EP : eval rho' PRODs = eval rho' (SVar 12)).
    { unfold PRODs. cbn [eval]. rewrite E143, E144. rewrite <- (proj1 Hag 12%positive) by (unfold NF; lia). rewrite E12c.
      unfold rho_c. rewrite !rw_set. unfold nwc. rewrite calloc_size_val. reflexivity. }
    set (KJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
    assert (H0 : SPA segs KJ (Lc_ok W st) rho' tp' w) by (split; [exact Hsm | exact I]).
    pose proof (proj1 Hsm) as Hs0. unfold virt in Hs0.
    pose proof (smatch_facts_hold _ _ _ _ Hs0) as HFa.
    assert (H1 : SPA segs KJ (ax_setS (Lc_ok W st) (Lconv_S W st)) rho' tp' w).
    { eapply SPA_restate; [exact Wcv | exact Dcv | reflexivity | | | exact H0].
      - constructor; [|constructor]. cbn [fst snd]. symmetry. exact EP.
      - constructor; [|constructor]. unfold F_topr. cbn [holds].
        assert (HT : holds rho' (SPUle (SAlu ALU_ADD (SVar V_RES) (SVar 12)) (SLit atop_hi))).
        { apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts ax_S Lc_ok Lc_ok_S mkA]. cbn [app]. unfold F_res_facts. cbn. tauto. }
        cbn [holds] in HT. cbn [eval] in HT |- *. cbn [eval] in EP. rewrite EP. exact HT. }
    assert (H2 : SPA segs KJ (ax_setX (ax_setS (Lc_ok W st) (Lconv_S W st)) [(SVar V_RES, PRODs)]) rho' tp' w).
    { apply (SPA_x_restate1 KJ rho' _ (SVar V_RES) (SVar 12) (SVar V_RES) PRODs [] tp' w); [reflexivity | reflexivity | exact EP | reflexivity | exact H1]. }
    change (ax_setX (ax_setS (Lc_ok W st) (Lconv_S W st)) [(SVar V_RES, PRODs)]) with (Lconv W st) in H2.
    exists (L_calloc_ok AE_A W st), (JL_calloc_ok AInv CST XGL A Kc), (rho_sub rho' s_fin), tp'.
    split; [right; left; reflexivity|]. split; [exact (fin_agree rho rho' Hag E143 E144)|].
    split; [exact (smatchA_entails segs _ _ s_fin rho' tp' w ENTcv (proj1 H2))|].
    unfold JL_calloc_ok. unfold JL_malloc_ok in HJ. destruct HJ as (A' & l1 & l2 & HA' & HL1 & HL2 & HF & HV & H4 & H5 & H6 & HM & HK & HC).
    exists A', l1, l2. rewrite ENV in HL1, HV, HC. rewrite Erm in HM.
    assert (ER : rw (rho_sub rho' s_fin) V_RES = rw rho' V_RES) by reflexivity.
    split; [unfold AInv, AInvA in *; rewrite (rm_rho_sub' rho' s_fin); exact HA'|].
    rewrite (rm_rho_sub' rho' s_fin), ER. repeat (split; [assumption|]). exact HC.
Qed.
End CONV.
End POSTS.
End CallocPosts.

