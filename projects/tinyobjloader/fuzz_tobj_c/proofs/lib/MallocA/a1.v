(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
From Stdlib Require NArith PArith.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.

(* [comment removed for export] *)
Module LedgerLaws.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "mul"; "modulo"; "pow"; "sub"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "length"; "bool"; "list"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "GAPC"; "FBMAX"; "NBMAX"; "hwN"; "hwS"; "GAPF"; "VCAP"; "gap_ok"; "ledger"; "GN"; "SLIM"; "N0"; "NLIM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_depot"; "AA"; "aa_V"; "dFB"; "dNB"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "page_size"; "Model"; "VmMaps"; "alloc_top"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_nZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "FBSZ"; "NBSZ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Placement.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma GAPC_lt : ltac2:(tb__ "0|1|
S0S14S6S5Z2M0Z40A2S5G0Z20A2A2A2").
Proof. unfold GAPC. lia. Qed.

Theorem gap_exists : ltac2:(tb__ "0|3|
S11S12SeQ40M0A1M1G1A2A1S8S0Z0M2R1A2S0S1S1S1S19R2A2S18R3A1A2S3S17R3A1S1R2ZfffA2A2A2S14A2SbS8S8SaS9S8S4R1S27A2G2A3SaS0S19R1A2SaS0S1R1R4A2S14A2S9S10S2bR5SdG0R1A2SdG0R4A2A3S13A3A2A2A2Lg;A2F_;F_;FnZ;Fl;").
Proof.
  intros l nZ HnZ Hroom.
  assert (HF0 : 0 <= GAPF) by (unfold GAPF; lia).
  destruct (scan l nZ GAPF GAPC HnZ HF0 GAPC_lt (length (List.filter (live_at GAPF) l)) GAPF (le_n _)) as (g & Hg).
  { split; [reflexivity|]. split; [lia|]. change (List.filter (live_at GAPF) l) with (live_hi l). rewrite gap_weight_hw. lia. }
  exists g. exact Hg.
Qed.

Lemma mmap_nZ_lit : ltac2:(tb__ "0|1|
S8SaS0Z0M0R1A2S7R1S5Z2Z40A2A2A2S9S8S4R2S27A2G0A3S9S8S2dSdQ40R3A2A1R3A3F_;F_;FnZ;").
Proof.
  intros nZ Hn Hal. unfold mmap_nZ. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64).
  rewrite Z.mod_small by lia. apply page_round_up_Z_id. exact Hal.
Qed.

Theorem place_of_room : ltac2:(tb__ "0|4|
S28S8S7Z0M0R1A2S9S8S4R2S27A2G0A3S0S14S2aS26R4A1A1A2S0S1S1S1S19R4A2S18S1cS26R5A1A1M1A1A2S3S17G1A1S1R4ZfffA2A2A2S14A2SbSeQ40M2A1M3G3S2cSdG2G0A2R7SdG2R6A2R1A4La;A2F_;F_;F_;F_;FnZ;Fmd;").
Proof.
  intros md nZ Hn Hal Htop Hroom.
  pose proof (hwS_nonneg (ledger (m_vmmaps md))) as S0'. pose proof (hwN_nonneg (ledger (m_vmmaps md))) as N0'.
  assert (HnZ64 : 0 <= nZ < 2 ^ 64) by (unfold GAPF, GAPC in Hroom; nia).
  destruct (gap_exists (ledger (m_vmmaps md)) nZ ltac:(lia) Hroom) as (g & Hgal & Hgf & Hgc & Hfree).
  exists (Z_to_bv 64 g). unfold mmap_place_ok_none. unfold GAPF, GAPC in *.
  assert (Eg : bv_unsigned (Z_to_bv 64 g) = g).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. lia. }
  rewrite Eg. rewrite (mmap_nZ_lit nZ HnZ64 Hal). unfold mmap_n. rewrite (mmap_nZ_lit nZ HnZ64 Hal).
  split; [exact Hgal|]. split; [lia|]. split; [lia|]. exact Hfree.
Qed.

Theorem room_of_gap_ok : ltac2:(tb__ "0|1|
S22S29S1bR2R1A2S0S23R3A1S1aA2S0S2SfS8S25S21R4A1A1A2A1S16A2S0S2SfS8S24S21R5A1A1A2A1S15A2SaS0S18S1cR5A1M0A1S1eA2S0S17G0A1S20A2A2F_;F_;F_;F_;FV;FA;").
Proof.
  intros A V [HN HS] HV HB1 HB2. unfold gapN_ok, gapS_ok, blocks_left in *.
  pose proof (hwN_nonneg (ledger V)). unfold GN, NBSZ, FBSZ in *. split; [lia | nia].
Qed.

Theorem count_of_gap_ok : ltac2:(tb__ "0|2|
S22S29S1bR2R1A2S0S2SfS8S25S21R3A1A1A2A1S16A2S0S2SfS8S24S21R4A1A1A2A1S15A2SaS0S3S1dS17S1cR4A1M0A1A2S1S3S1dS1S1S1S1fS16A2S15A2Z1A2A2S23R5A1M1A2A2S0S18G0A1S6S1eS3Z2S6S1aG1A2A2A2A2A2F_;F_;F_;FV;FA;").
Proof.
  intros A V [HN HS] HB1 HB2. unfold gapN_ok, gapS_ok, blocks_left, NLIM in *.
  pose proof (hwN_nonneg (ledger V)). pose proof (Z.div_mod VCAP GN ltac:(unfold GN; lia)). pose proof (Z.mod_pos_bound VCAP GN ltac:(unfold GN; lia)).
  unfold GN, NBSZ, FBSZ in *. split; [nia | lia].
Qed.

Theorem depot_place : ltac2:(tb__ "0|2|
S22S28S8S1bR3S26R2A1A2S0S23R4A1S1aA2S0S2SfS8S25S21R5A1A1A2A1S16A2S0S2SfS8S24S21R6A1A1A2A1S15A2S0S14S2aS26R6A1A1A2ScS9S8R6S2fA3S9S8R6S2eA3A2SbSeQ40M0A1M1G1S2cSdG0Z0A2R9SdG0R8A2R1A4La;A2F_;F_;F_;F_;F_;F_;FL;Fmd;FA;").
Proof.
  intros A md L HG HV HB1 HB2 Htop HL.
  destruct (room_of_gap_ok A (m_vmmaps md) HG HV HB1 HB2) as [HS HN].
  pose proof gap_closes as CL. pose proof (hwN_nonneg (ledger (m_vmmaps md))) as N0'.
  apply place_of_room; [unfold NBSZ, FBSZ in HL; lia | destruct HL as [-> | ->]; reflexivity | exact Htop |].
  assert (HLB : 0 < L <= FBSZ) by (unfold NBSZ, FBSZ in HL |- *; lia).
  unfold FBSZ in *. nia.
Qed.
End LedgerLaws.

(* [comment removed for export] *)
Module SegQ1_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "bool"; "false"; "prod"; "true"; "list"; "app"; "andb"; "None"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "SVar"; "sprop"; "cell"; "mkCell"; "SPAlign"; "DUnknown"; "FcsrFrm0"; "SAlu"; "SPUle"; "mkObj"; "mkSS"; "ss_lenient"; "ss_next"; "swf"; "SPBranch"; "SPNot"; "SPUlt"; "SExt"; "ss_pc"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "NPRE"; "vPK"; "CREF"; "O_qc"; "runA"; "vQB"; "vQN"; "vQS"; "PreQ1A"; "PreQ1Be"; "PreQ1Bf"; "nb_base"; "vQF"; "O_bh"; "O_nb"; "O_pc24"; "O_pck"; "O_sb"; "O_st"; "RETQ"; "vBS"; "vK"; "vSB"; "vST"; "F_B"; "chk1p"; "mkPost"; "mkPre"; "szb"; "vCS"; "vNX"; "F_A"; "F_Bf"; "F_Q"; "NXQ"; "O_item"; "nb_cells"; "run_A"; "run_Be"; "run_Bf"; "sz"; "vCP"; "C24OFF"; "DEPTH_Q"; "DUMMY"; "ENQ"; "PostQ1A"; "PostQ1Be"; "PostQ1Bf"; "cp_base"; "ents"; "item_base"; "leaf"; "post_ru"; "single_ret"; "vMX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axwf"; "la_state"; "entailsA"; "la_reason"; "mkLeafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SLL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mkA"; "A_globals"; "stack_win"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "RsCut"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "eqb"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "HIGH_SHADOW_END"; "kSpaceSize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Open Scope Z_scope.

Definition ENQ : Z := 0x40834.
Definition RETQ : Z := 0x40950.
Definition CREF : Z := 0x40954.
Definition OOMQ : Z := 0x409a8.
Definition DEPTH_Q : Z := 1024.
Definition NPRE : positive := 160%positive.
Definition NXQ : positive := 230%positive.
Definition C24OFF : Z := 24 * 2 ^ 32.

Definition add (a b : sv) : sv := SAlu ALU_ADD a b.

Definition vQN := SVar 120.
Definition vQF := SVar 121.
Definition vQB := SVar 122.
Definition vQS := SVar 123.
Definition vNX := SVar 124.
Definition vBS := SVar 125.
Definition vK  := SVar 126.
Definition vPK := SVar 127.
Definition vMX := SVar 128.
Definition vCS := SVar 129.
Definition vCP := SVar 130.
Definition vST := SVar 131.
Definition vSB := SVar 155.

Definition DUMMY : leafA := ltac2:(tb__ "0|1|
S66S6bS1aZ0S2SeA1M0G0S16SbSeA1S2SdA1S2S11A1S4aS5A9S2S6SeSeA2A1A2S74A2").
Definition leaf (i : nat) (l : list leafA) : axst := ltac2:(tb__ "0|0|
S63S77S61Vi;Vl;S54A4A1").
Definition runA (fuel : nat) (cuts : list Z) (A : axst) : list leafA := ltac2:(tb__ "0|1|
ScS8S61A1M0A1G0Lx;S67S79Vfuel;Vcuts;VA;S7A5G0R1Ll;S2S61A1Xcx2").

Definition O_qc (qn qf qb qs : sv) : sobj := ltac2:(tb__ "0|4|
S68S10PcA1Z0M0Z20S0S6S6S23S3A2M1SeA2M2S1G1SeS1S23S3G0U8M3A4Vqn;A4S0G2S1G1SeS1S23S3Z8G3A4Vqf;A4S0G2S1G1SeS1S23S3Z10G3A4Vqb;A4S0G2S1G1SeS1S23S3Z18G3A4Vqs;A4S2G2A1A3A3A3A3A4").
Definition O_bh (nx bs k : sv) : sobj := ltac2:(tb__ "0|4|
S68S2dZ0M0Z18S0S6S6S23S3A2M1SeA2M2S1G1SeS1S23S3G0U8M3A4Vnx;A4S0G2S1G1SeS1S23S3Z8G3A4Vbs;A4S0G2S1G1SeS1S23S3Z10G3A4Vk;A4S2G2A1A3A3A3A4").

Definition item_base : sv := ltac2:(tb__ "0|0|
S27S2dS17S69S3dSfZ3A1A3A2").
Definition O_item (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S5bSfZ18A1SfZ20A1Vcells;S15A5").
Definition O_pc24 (k : sv) : sobj := ltac2:(tb__ "0|4|
S68S10PdA1Z780M0Z790S0S6S6S23S3A2M1SeA2M2S1G1SeS1S23S3G0U4M3A4Vk;A4S0G2S1G1SeS1S23S3Z784G3A4S5fA4S0G2S1G1SeS1S23S3Z788U8A4S45A4S2G2A1A3A3A3A4").

Definition cp_base : sv := ltac2:(tb__ "0|0|
S27S10PdA1S17S69S27S29SfN1A1A2SfZ2A1A3A2").
Definition O_pck : sobj := ltac2:(tb__ "0|1|
S19S59SfZ790A1M0SfZ794A1S0S12S13G0Z4S51A3S2S12A1A3S15A5").
Definition O_st (v : sv) : sobj := ltac2:(tb__ "0|3|
S68S10PdA1Za10M0Za18S0S6S6S23S3A2M1SeA2M2S1G1SeS1S23S3G0U8A4Vv;A4S2G2A1A3A4").
Definition O_sb : sobj := ltac2:(tb__ "0|3|
S68SfZ0A1Zeddb8M0Zeddc0S0S6S6S23S3A2M1SeA2M2S1G1SeS1S23S3G0U8A4S3eA4S2G2A1A3A4").

Definition nb_base : sv := ltac2:(tb__ "0|0|
S27S17S69S21S5Q20S51A3SfZ4A1A3S27S3eSfS52A1A2A2").
Definition O_nb (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S19S33SfZ0A1SfZ2000A1Vcells;S15A5").

Definition F_Q : list sprop := ltac2:(tb__ "0|0|
S9S11S6eS53A1S0S11S14PcZ3A2S2S11A1A3A3").
Definition F_A : list sprop := ltac2:(tb__ "0|0|
S9S11S49S0S11S14P7aZ3A2S0S11S1fS1eS6aS2eSfZ0A1A3A1S0S11S20S3dSfZ3fdA1A2S2S11A1A3A3A3A3").
Definition F_B : list sprop := ltac2:(tb__ "0|0|
S9S11S49S0S11S14PdZ4A2S0S11S20SfZ0A1S29A2S0S11S18S29SfZ100A1A2S0S11S14P9bZ10A2S0S11S18SfS7aA1S3eA2S0S11S18S3eSfS75S75Z7fffff800000S7bA2Z1000A2A1A2S2S11A1A3A3A3A3A3A3A3").
Definition F_Bf : list sprop := ltac2:(tb__ "0|0|
S9S11S40S0S11S14P7aZ3A2S0S11S1fS1eS6aS2eSfZ0A1A3A1S2S11A1A3A3A3").

Definition mkPre (objs : list sobj) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S6bS1aS55S70S6fS16SbSeA1S9SdS0SdS6dVobjs;A3S6cA3VF;S28S5A9S2S6SeSeA2A1A2").
Definition PreQ1A : axst := ltac2:(tb__ "0|0|
S43S0SdS2bS2eS34S2dS2fA4S0SdS35S46S3cS3dA3S0SdS4bS2S12A1A1S2SdA1A3A3A3S47A2").
Definition PreQ1Be : axst := ltac2:(tb__ "0|0|
S43S0SdS2bSfZ0A1S34S2dS2fA4S0SdS37S29A1S0SdS38S0SdS3aS3fA1S0SdS39S0SdS36S2S12A1A1S2SdA1A3A3A3A3A3A3S40A2").
Definition PreQ1Bf : axst := ltac2:(tb__ "0|0|
S43S0SdS2bS2eS34S2dS2fA4S0SdS35S46S3cSfZ3fdA1A3S0SdS37S29A1S0SdS38S0SdS3aS3fA1S0SdS39S0SdS36S2S12A1A1S2SdA1A3A3A3A3A3A3A3S48A2").

Definition post_ru : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S3SeA2M0S1S3SeU5S10Pb9A1A4S0G0S1S3SeU6S10PbaA1A4S0G0S1S3SeU7S10PbbA1A4S0G0S1S3SeUaS10PbcA1A4S0G0S1S3SeUbS10PbdA1A4S0G0S1S3SeUcS10PbeA1A4S0G0S1S3SeUdS10PbfA1A4S0G0S1S3SeUeS10Pc0A1A4S0G0S1S3SeUfS10Pc1A1A4S0G0S1S3SeU10S10Pc2A1A4S0G0S1S3SeU11S10Pc3A1A4S0G0S1S3SeU1cS10Pc4A1A4S0G0S1S3SeU1dS10Pc5A1A4S0G0S1S3SeU1eS10Pc6A1A4S0G0S1S3SeU1fS10Pc7A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition mkPost (objs : list sobj) (F : list sprop) : axst := ltac2:(tb__ "0|0|
S6bS1aS3bS71S70S5dA2S6fS16SbSeA1S9SdS0SdS6dVobjs;A3S6cA3VF;S4aS5A9S2S6SeSeA2A1A2").
Definition sz : sv := SVar 34.
Definition szb : sv := add sz (SLit 8192).
Definition PostQ1A : axst := ltac2:(tb__ "0|0|
S42S0SdS2bS2eS34S2dS27S2fS50A2A4S0SdS35S46S27S3cS50A2S27S3dSfZ1A1A2A3S0SdS4bS0S12S13SfZ18A1Z8S10P21A1A3S2S12A1A3A1S2SdA1A3A3A3S47A2").
Definition nb_cells : list cell := ltac2:(tb__ "0|2|
S0S12S13SfZ0A1M0Z8M1G0A3S0S12S13SfG1A1G1S44A3S0S12S13SfZ10A1G1SfZ1A1A3S0S12S13SfZ18A1G1S10P21A1A3S2S12A1A3A3A3A3").
Definition PostQ1Be : axst := ltac2:(tb__ "0|0|
S42S0SdS2bSfZ1A1S33S33S27S2fS44A2A4S0SdS37S27S29SfN1A1A2A1S0SdS38S0SdS3aS27S3fS45A2A1S0SdS39S0SdS36S4cA1S2SdA1A3A3A3A3A3A3S40A2").
Definition PostQ1Bf : axst := ltac2:(tb__ "0|0|
S42S0SdS2bS27S2eSfZ1A1A2S34S33S27S2fS44A2A4S0SdS35S33S3cSfZ3fdA1A3S0SdS37S27S29SfN1A1A2A1S0SdS38S0SdS3aS27S3fS45A2A1S0SdS39S0SdS36S4cA1S2SdA1A3A3A3A3A3A3A3S48A2").

Definition run_A : list leafA := ltac2:(tb__ "0|0|
S2cU190S0S23S2aS2S23A1A3S30A3").
Definition run_Be : list leafA := ltac2:(tb__ "0|0|
S2cU190S0S23S2aS2S23A1A3S31A3").
Definition run_Bf : list leafA := ltac2:(tb__ "0|0|
S2cU190S0S23S2aS2S23A1A3S32A3").
Definition ents (L T : axst) : bool := ltac2:(tb__ "0|0|
S64VL;VT;S72S28S60VL;A1S60VT;A1A3A3").
Definition single_ret (retpc : Z) (l : list leafA) : bool := ltac2:(tb__ "0|1|
S8S61A1M0S4Ll;Vl;S5S61G0G0S4Ll0;R1SaS76S22S60S63R2A1A1A1Vretpc;A2S73S4Lx;S65R2A1S5S5S5S5S7S5S5X73x7A2S61G0S5Ll2;Ll1;X8x2Ll0;LL;X8x2").

Definition chk1p (retpc : Z) (l : list leafA) (P : axst) : bool := ltac2:(tb__ "0|1|
SaSaSaS5eVretpc;Vl;A2S5aS5cU0Vl;A2M0VP;A2A2S78S72S28S60G0A1S60VP;A1A3S28A2A2S62VP;A1A2").
Definition chk1 : list leafA -> axst -> bool := chk1p RETQ.

Lemma run_A_eq : ltac2:(tb__ "0|0|
S25S8S61A1S2cU190S0S23S2aS2S23A1A3S30A3S4dA3").    Proof. unfold run_A. reflexivity. Qed.
Lemma run_Be_eq : ltac2:(tb__ "0|0|
S25S8S61A1S2cU190S0S23S2aS2S23A1A3S31A3S4eA3"). Proof. unfold run_Be. reflexivity. Qed.
Lemma run_Bf_eq : ltac2:(tb__ "0|0|
S25S8S61A1S2cU190S0S23S2aS2S23A1A3S32A3S4fA3"). Proof. unfold run_Bf. reflexivity. Qed.
Lemma pre_nx : ltac2:(tb__ "0|3|
S26S25S24S1cS60S30A1M0A1S28A3S26S25S24S1cS60S31A1M1A1S28A3S26S25S24S1cS60S32A1M2A1S28A3S26S25S4S1bG0A1S5A3S26S25S4S1bG1A1S5A3S25S4S1bG2A1S5A3A2A2A2A2A2").
Proof. repeat split; reflexivity. Qed.

Lemma chk_A : ltac2:(tb__ "0|0|
S25S4S41S3bS4dS56A3S7A3").   Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_Be : ltac2:(tb__ "0|0|
S25S4S41S3bS4eS57A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_Bf : ltac2:(tb__ "0|0|
S25S4S41S3bS4fS58A3S7A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma pre_wf : ltac2:(tb__ "0|0|
S26S25S4S62S30A1S7A3S26S25S4S62S31A1S7A3S25S4S62S32A1S7A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma pre_swf : ltac2:(tb__ "0|0|
S26S25S4S1dS60S30A1A1S7A3S26S25S4S1dS60S31A1A1S7A3S25S4S1dS60S32A1A1S7A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SegQ1_states.

(* [comment removed for export] *)
Module InvInitC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "enc_bytes"; "eval"; "image_byte"; "rm"; "smatch"; "ss_objs"; "sv_eqb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "eqb"; "le"; "lt"; "@Corelib.Init.Datatypes"; "bool"; "option"; "true"; "nat"; "Some"; "prod"; "andb"; "false"; "list"; "pair"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "binfo"; "byte_is"; "lit_byte"; "BImg"; "zseq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "filled"; "mkACell"; "present"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes"; "cell_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB"; "range_info"; "range_present"; "range_zero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.InvInitC"; "lit_cell_is"; "sym_cell_is"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA Virt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvInitB.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvInitB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.StartHandoffBytes.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition lit_cell_is (L : list sobj) (base : sv) (off : Z) (w : nat) (val : Z) : bool := ltac2:(tb__ "0|0|
S34S0S0S1fS1dVL;Vbase;ScVoff;R1A2S20Vval;R1A2A5Lj;S22Z0Vw;A2A3").
Definition sym_cell_is (L : list sobj) (base : sv) (off : Z) (w : nat) (e : sv) : bool := ltac2:(tb__ "0|1|
S12S16S0S3A2M0A1S11Lx;S2dVL;Vbase;Voff;A3G0G0S11Lp;R1S0S3S17SeR2SdVw;A1A2SbR1Ve;A2A2Lv;Lwd;X16x1Lp;S18X12x2").

Section C.
Variables (rho1 rhoM : valuation) (S : sstate) (tr : list event) (ms : machine_state) (md : Model).
Hypothesis Hsm : ltac2:(tb__ "0|0|
S9S1dVrho1;VS;S1aS19S2cA1S2aVtr;S2bVms;Vmd;A2A4A4").
Hypothesis Hrm : ltac2:(tb__ "0|0|
S1cQ40A1S2eVrho1;SaVS;A1R1A3S1S12S1cQ8A1A1S8VrhoM;R2A2S29Vms;R2A2A3F_;Fa;").
Let L : list sobj := ss_objs S.
Let m : bview := view segsA (rm rhoM).
Let U (e : sv) : Z := bv_unsigned (eval rho1 e).

Lemma hbyte : ltac2:(tb__ "0|2|
S3S0S0S1S11S1fS1dVL;R3R2R1A5S13A3S1S12S1cQ8M0A1M1A1Vm;ScVU;R4A1R3A2A1S15G1S1bG0R2A2A2A3F_;Fv;Foff;Fbase;").
Proof.
  intros base off v H. unfold byte_is in H.
  destruct (byte_info L base off) as [| |v'|] eqn:E; try discriminate.
  - pose proof (handoff_view rho1 rhoM S tr ms md base off Hsm Hrm ltac:(fold L; rewrite E; discriminate)) as X. cbv zeta in X.
    fold L in X. rewrite E in X. destruct X as (_ & _ & X). apply Z.eqb_eq in H. unfold m, U. rewrite X. f_equal. apply Z_to_bv8_mod256. exact H.
  - apply andb_prop in H as [Hb Hi]. apply sv_eqb_sound in Hb. subst base.
    pose proof (handoff_view rho1 rhoM S tr ms md (SLit 0) off Hsm Hrm ltac:(fold L; rewrite E; discriminate)) as X. cbv zeta in X.
    fold L in X. rewrite E in X. destruct X as (R & _ & Hn & _). unfold m, U.
    assert (E0 : bv_unsigned (eval rho1 (SLit 0)) = 0) by (cbn [eval]; rewrite Z_to_bv_unsigned; reflexivity).
    rewrite E0 in *. rewrite Z.add_0_l in *. rewrite (view_in segsA _ _ R). unfold rd_of. rewrite Hn.
    destruct (image_byte segsA (Z_to_bv 64 off)) as [b|]; [|discriminate]. apply Z.eqb_eq in Hi. f_equal.
    apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact Hi.
Qed.

Lemma enc_lit_byte : ltac2:(tb__ "0|2|
S14S14S0S27R2R3A2S1S1cQ8M0A1M1S28G1R3S5R4S1bQ40R2A2A2S1bG0Z0A2A4S1bG0S20R2SdR3A1A2A2A3F_;Fval;Fk;Fw;").
Proof.
  intros w k val Hk. unfold enc_bytes. rewrite Z_to_le_bytes_nth by exact Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z_to_bv8_mod256. unfold lit_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma hcell_lit : ltac2:(tb__ "0|0|
S3S0S14S0S1S11S32VL;R4R3R2R1A5S13A3S23Vm;S25ScVU;R5A1R4A2R3R2A3A2F_;Fval;Fw;Foff;Fbase;").
Proof.
  intros base off w val H k Hk. cbn [c_addr c_w c_val] in *. unfold lit_cell_is in H.
  pose proof (proj1 (forallb_forall _ _) H (Z.of_nat k) ltac:(apply In_zseq; lia)) as X.
  rewrite (enc_lit_byte w k val Hk). rewrite <- Z.add_assoc. exact (hbyte base (off + Z.of_nat k) _ X).
Qed.

Lemma hcell_sym : ltac2:(tb__ "0|1|
S3S0S14S3S0S1S11S33VL;R5R4R3R2A5S13A3S1S1cQ40M0A1S6Vrho1;R3A2S1bG0R2A2A3S23Vm;S25ScVU;R7A1R6A2R5R3A3A2F_;F_;Fval;Fe;Fw;Foff;Fbase;").
Proof.
  intros base off w e val H Ev k Hk. cbn [c_addr c_w c_val] in *. unfold sym_cell_is in H.
  destruct (cell_info L base off) as [[wd v]|] eqn:E; [|discriminate]. apply andb_prop in H as [Hw Hv].
  apply Z.eqb_eq in Hw. apply sv_eqb_sound in Hv. subst v wd.
  pose proof (handoff_cell rho1 rhoM S tr ms md base off _ e Hsm Hrm E) as X. cbv zeta in X. destruct X as (_ & _ & X).
  rewrite Nat2Z.id in X. unfold m, U. rewrite (X k Hk), Ev. reflexivity.
Qed.

Lemma hrange_zero : ltac2:(tb__ "0|1|
S3S0S0S1S11S31VL;R3R2R1A4S13A3S24Vm;ScVU;R4A1M0R3A2ScG0R2A2Z0A4F_;Fb;Fa;Fbase;").
Proof.
  intros base a b H z Hz. pose proof (range_zero_spec L base a b H (z - U base) ltac:(lia)) as E.
  pose proof (handoff_view rho1 rhoM S tr ms md base (z - U base) Hsm Hrm ltac:(fold L; rewrite E; discriminate)) as X. cbv zeta in X.
  fold L in X. rewrite E in X. destruct X as (_ & _ & X). unfold m. replace z with (U base + (z - U base)) by lia. exact X.
Qed.
Lemma hrange_present : ltac2:(tb__ "0|1|
S3S0S0S1S11S30VL;R3R2R1A4S13A3S26Vm;ScVU;R4A1M0R3A2ScG0R2A2A3F_;Fb;Fa;Fbase;").
Proof.
  intros base a b H z Hz. pose proof (range_present_spec L base a b H (z - U base) ltac:(lia)) as E.
  pose proof (handoff_view rho1 rhoM S tr ms md base (z - U base) Hsm Hrm E) as X. cbv zeta in X.
  destruct X as (_ & X & _). unfold m. replace z with (U base + (z - U base)) by lia. exact X.
Qed.

Lemma hrange_img_zero : ltac2:(tb__ "0|3|
S0S0S1S12S1eA1S2fVL;S4Z0M0A1R2R1A4S15S1eS21A2A3S0S2SfR4R1A2S10R1R3A2A2S1S12S1cQ8M1A1M2A1S7S1dS1bQ40R2A2A2S15G2S1bG1G0A2A2A3F_;Fx;S24Vm;R4R3G0A4F_;F_;Fb;Fa;").
Proof.
  intros a b H HI z Hz. pose proof (range_info_spec L (SLit 0) a b BImg H z Hz) as E.
  pose proof (handoff_view rho1 rhoM S tr ms md (SLit 0) z Hsm Hrm ltac:(fold L; rewrite E; discriminate)) as X. cbv zeta in X.
  fold L in X. rewrite E in X. destruct X as (R & _ & Hn & _).
  assert (E0 : bv_unsigned (eval rho1 (SLit 0)) = 0) by (cbn [eval]; rewrite Z_to_bv_unsigned; reflexivity).
  rewrite E0, Z.add_0_l in R, Hn. unfold m. rewrite (view_in segsA _ _ R). unfold rd_of. rewrite Hn. exact (HI z Hz).
Qed.
End C.
End InvInitC.

(* [comment removed for export] *)
Module CertStackMalloc.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SAlu"; "SVar"; "SPUle"; "cell"; "mkCell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "SPUlt"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "prod"; "nil"; "app"; "bool"; "None"; "false"; "andb"; "list"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vFSB"; "vHINT"; "vT"; "vCTX"; "vH"; "vK"; "TP_A"; "vDTLS"; "RT_objs"; "NWF"; "vBOT"; "vTOP"; "F_winB"; "O_T0"; "O_T30"; "O_T40"; "O_T48"; "O_cfa"; "O_cfb"; "O_cfc"; "O_cfd"; "O_cfe"; "O_ctx8"; "O_ctx98"; "O_dtls"; "O_fsh_h"; "O_fsh_l"; "O_pga"; "O_pgb"; "O_realtls"; "O_rt1a"; "O_rt1b"; "O_self_tsd"; "O_tlsa"; "O_tlsb"; "O_tlsc"; "O_tlsd"; "O_tsd0"; "O_tsda"; "O_tsdb"; "O_tsdc"; "RT_fixed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"; "FS_LOG"; "FS_frames_off"; "FS_total"; "IMG_HI"; "K_HIGH_MEM_END"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kMallocContextSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc.Win"; "MASK"; "F_K"; "NIT"; "ffx"; "Cst"; "O_flagc"; "FLOFF"; "F_geom"; "POS"; "flagaddr"; "loopheads"; "Cgen"; "F_found"; "O_flagw"; "O_frame"; "O_fshadow"; "O_own"; "busy_scratch"; "Cbusy"; "Cfree"; "Ebusy"; "Efree"; "Efree_objs"; "P0"; "X0"; "init_scratch"; "loop_pc"; "loop_ra"; "ltempl"; "ret_regs"; "zero_cells"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "div"; "add"; "mul"; "eqb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "NW"; "GW"; "segsA"; "F_win"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "mkA"; "AE_A"; "V_DEPTH"; "ae_ret_stack_malloc"; "ae_stack_malloc"; "pre_facts"; "stack_malloc_depth"; "stack_win"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymCFG ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition vT : sv := SVar 151. Definition vCTX : sv := SVar 152. Definition vTOP : sv := SVar 153. Definition vBOT : sv := SVar 154.
Definition vFSB : sv := SVar 155. Definition vDTLS : sv := SVar 156. Definition vHINT : sv := SVar 157.
Definition vH : sv := SVar 158. Definition vK : sv := SVar 159.

Definition vGF : positive := 200%positive.
Definition NWF : positive := 201%positive.
Definition TP_A : Z := 0x6245b8.

Definition O_rt1a : sobj := ltac2:(tb__ "0|5|
S1cS1Z0A1Zf20d8M0Zf20daSfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1M3A4S1Z1A1M4A4SfG2S10G1S0S10S1aS11Zf20d9G3A4G4A4S13G2A1A3A3A4").
Definition O_rt1b : sobj := ltac2:(tb__ "0|5|
S1cS1Z0A1M0Zf20e0M1Zf20f8SfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U8M4A4S1S50A1A4SfG3S10G2S0S10S1aS11Zf20e8G4A4G0A4SfG3S10G2S0S10S1aS11Zf20f0G4A4G0A4S13G3A1A3A3A3A4").

Definition O_mcs : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Zf20fcM0Zf2100SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U4A4S1S54A1A4S13G2A1A3A4").
Definition O_tsda : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Zf0c5cM0Zf0c5dSfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Z1A1A4S13G2A1A3A4").
Definition O_tsdb : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Zf0c60M0Zf0c61SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Z1A1A4S13G2A1A3A4").
Definition O_tsdc : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1M0Zf0c64M1Zf0c68SfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U4A4G0A4S13G3A1A3A4").
Definition O_realtls : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Ze9a20M0Ze9a28SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1Zdeb68A1A4S13G2A1A3A4").
Definition O_self_tsd : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z624560M0Z624568SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1Z645960A1A4S13G2A1A3A4").
Definition O_tlsa : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1Z6245b0M0Z6245c0SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8M3A4S1Z6245d8A1A4SfG2S10G1S0S10S1aS11Z6245b8G3A4S21A4S13G2A1A3A3A4").
Definition O_tlsb : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z6245c0M0Z6245c8SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S28A4S13G2A1A3A4").
Definition O_tlsc : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1M0Z6245c8M1Z6245ccSfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U4A4G0A4S13G3A1A3A4").
Definition O_tlsd : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z6245e0M0Z6245e8SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1Z624db8A1A4S13G2A1A3A4").
Definition O_tsd0 : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z645960M0Z645968SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S24A4S13G2A1A3A4").
Definition O_ctx8 : sobj := ltac2:(tb__ "0|3|
S1cS24Z8M0ZcSfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U4A4S1Z0A1A4S13G2A1A3A4").
Definition O_ctx98 : sobj := ltac2:(tb__ "0|3|
S1cS24Z98M0Za0SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S23A4S13G2A1A3A4").
Definition O_T0 : sobj := ltac2:(tb__ "0|4|
S1cS23Z0M0Z18SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8M3A4S24A4SfG2S10G1S0S10S1aS11Z8G3A4S2cA4SfG2S10G1S0S10S1aS11Z10G3A4S2bA4S13G2A1A3A3A3A4").
Definition O_T40 : sobj := ltac2:(tb__ "0|3|
S1cS23Z28M0Z29SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Z0A1A4S13G2A1A3A4").
Definition O_T30 : sobj := ltac2:(tb__ "0|4|
S1cS23Z30M0Z40SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8M3A4S1Z624cf0A1A4SfG2S10G1S0S10S1aS11Z38G3A4S1Z624dccA1A4S13G2A1A3A3A4").
Definition O_T48 : sobj := ltac2:(tb__ "0|3|
S1cS23Z48M0Z50SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S21A4S13G2A1A3A4").
Definition O_dtls : sobj := ltac2:(tb__ "0|3|
S1cS28Z18M0Z20SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1S27A1A4S13G2A1A3A4").
Definition O_cfa : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z182f4aM0Z182f4bSfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Z1A1A4S13G2A1A3A4").
Definition O_cfb : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z182fa0M0Z182fa8SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1ZffffffffffffffffA1A4S13G2A1A3A4").
Definition O_cfc : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z182fb1M0Z182fb2SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Z1A1A4S13G2A1A3A4").
Definition O_cfd : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1M0Z182fb8M1Z182fc0SfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U8A4G0A4S13G3A1A3A4").
Definition O_cfe : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1M0Z18302cM1Z18302dSfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U1A4G0A4S13G3A1A3A4").
Definition O_pga : sobj := ltac2:(tb__ "0|4|
S1cS1Z0A1M0Z180e98M1Z180e9cSfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U4A4G0A4S13G3A1A3A4").
Definition O_pgb : sobj := ltac2:(tb__ "0|3|
S1cS1Z0A1Z180ea0M0Z180ea8SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1S51A1A4S13G2A1A3A4").

Definition O_fsh_h (c : Z) (h : sv) : sobj := ltac2:(tb__ "0|4|
S1cS21S77Z8M0Vc;A2M1S76G1G0A2SfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11G1U8A4Vh;A4S13G3A1A3A4").
Definition O_fsh_l : sobj := ltac2:(tb__ "0|3|
S1cS21Z58M0Z61SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U8A4S1S4cA1A4SfG2S10G1S0S10S1aS11Z60U1A4S1Z0A1A4S13G2A1A3A3A4").
Definition RT_fixed : list sobj := ltac2:(tb__ "0|0|
SfS2S3fSfS2S40SfS2S47SfS2S48SfS2S49SfS2S3eSfS2S41SfS2S42SfS2S43SfS2S44SfS2S45SfS2S46SfS2S37SfS2S38SfS2S2eSfS2S30SfS2S2fSfS2S31SfS2S39SfS2S32SfS2S33SfS2S34SfS2S35SfS2S36SfS2S3cSfS2S3dSfS2S3bS13S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition RT_objs (c : Z) (h : sv) : list sobj := ltac2:(tb__ "0|0|
S14S2S4aSfS2S3aVc;Vh;A2S13S2A1A3A3").

Definition F_winB (hi : bool) (e : sv) (len : Z) : list sprop := ltac2:(tb__ "0|1|
S15S19S3A1Lhi;Vhi;SfS3S6S1S52A1Ve;A2SfS3S6Ve;S1S74Z7fffff800000Vlen;A2A1A2S13S3A1M0A3A3SfS3S6S1S4fA1Ve;A2SfS3S6Ve;S1S74S53Vlen;A2A1A2G0A3A3X15x2").

Section Win.
Variable hi : bool.

Definition F_geom : list sprop := ltac2:(tb__ "0|5|
S14S3SfS3SdS2bS2cA2SfS3S6S1Z1000M0A1M1S23A2SfS3S6S23S1S74Z7fffff800000G0A2A1M2A2SfS3SbP97ZcM3A2SfS3S6G1S24A2SfS3S6S24G2A2S13S3A1M4A3A3A3A3A3A3S14S3S2dVhi;S21S4eA3S14S3SfS3SbP9bG3A2SfS3S6G1S28A2SfS3S6S28G2A2G4A3A3A3S8cS8dA1A3A3A3").

Definition P0 (c : Z) : axst := ltac2:(tb__ "0|1|
S87SaS8bS88Vc;A2S82S83SfS12S11S0A2M0S10S11S0U4S1S27A1A4S13G0A1A3A2S81S9S16S0A1S14S2SfS2S8eS13S2A1A3S14S2S86S29Vc;S22A2A3A3S14S3SfS3S6S5PcA1S1S4bVc;A1A1A2S13S3A1A3S5cA3S7bS17A9S13S12S0S0A2A1A2").

Definition loop_pc (c : Z) : Z := match c with 0 => 0x4798c | 1 => 0x47b10 | 2 => 0x47ca0 | 3 => 0x47e3c | 5 => 0x47fe8 | 6 => 0x482a8 | _ => 0 end.
Definition loop_ra (c : Z) : Z := match c with 0 => 293164 | 1 => 293536 | 2 => 293936 | 3 => 294348 | 5 => 294776 | 6 => 295480 | _ => 0 end.
Definition NIT (c : Z) : Z := fs_num_iter c.
Definition MASK (c : Z) : Z := fs_num_iter c - 1.
Definition FLOFF (c : Z) : Z := fs_flags 0 c.
Definition ltempl (c : Z) (K H t0 s1 s2 : sv) : list sv := ltac2:(tb__ "0|10|
S82S83S14S12S11S0A2M0SfG0S10S11S0U1S1S70Vc;A1A1A4SfG0S10S11S0U2S4S1dS5PaA1M1S1N20A1A3A4SfG0S10S11S0U4S1S27A1A4SfG0S10S11S0U8G1A4SfG0S10S11S0U9S21A4SfG0S10S11S0UaVK;A4SfG0S10S11S0UbS4S1dS21S1Z1000A1A3A4SfG0S10S11S0UcVH;A4SfG0S10S11S0U12S1S4cA1A4S13G0A1M2A3A3A3A3A3A3A3A3A3S1aS19G0A1M3Lc;Vc;SfG0S10S11S0UdM4S1S55Z0M5A1A1A4SfG0S10S11S0UeM6S4S1dS22S1S57G5A1A1A3A4SfG0S10S11S0UfM7Vs1;A4M8SfG0S10S11S0U10M9Vs2;A4SfG0S10S11S0U11MaVt0;A4G2A3A3A3A3A3S1bS1bG3Lp;R1S1bSfG0S10S11S0U5Vt0;A4MbSfG0S10S11S0G4S4S1dS21S1S5bVc;A1A1A3A4SfG0S10S11S0G6S1S55Vc;A1A1A4SfG0G8SfG0S10S11S0G9S4S1dS22S1S57Vc;A1A1A3A4SfG0S10S11S0GaVs2;A4G2A3McA3A3A3A3A3MdLp0;S1bS1bG3Lp0;R1S1bS1bG3Lp1;R1S1bGdLp2;MeGeSfG0GbSfG0S10S11S0G4S4S1dS21S1S5bZ6MfA1A1A3A4SfG0S10S11S0G6Vs1;A4SfG0S10S11S0G7S1S55GfA1A1A4SfG0S10S11S0G9S4S1dS22S1S57GfA1A1A3A4GcA3A3A3A3A3X1bx3Lp1;S1bGdLp1;GdX1bx3Lp0;GdX1bx3Lp;S1bGdLp;X1ax3A3A2").

Definition init_scratch (c : Z) : sv * sv * sv := ltac2:(tb__ "0|6|
S1aS12S12S0S0A2M0S0A2M1Lc;Vc;S10G0S0S10S0S0S5P25A1M2S1S55Z0A1A1A4S5P24A1A4S1bS1bG1Lp;R1S1bS10G0S0S10S0S0S5P19A1M3S4S1dS22S1S55Vc;A1A1A3A4G2A4M4Lp0;S1bS1bG1Lp0;R1S1bS1bG1Lp1;R1S1bG4Lp2;M5G5S10G0S0S10S0S0G3S4S1dS22S1S55Z6A1A1A3A4G2A4X1bx3Lp1;S1bG4Lp1;G4X1bx3Lp0;G4X1bx3Lp;S1bG4Lp;X1ax3").

Definition O_own : sobj := ltac2:(tb__ "0|1|
SeS5PaA1S5S89A1S1Z0A1SfS7S8S1N8A1Z8M0S5PbA1A3SfS7S8S1N10A1G0S5P1cA1A3SfS7S8S1N18A1G0S5P1dA1A3SfS7S8S1N20A1G0S5P26A1A3S13S7A1A3A3A3A3ScA5").

Definition Cst (nx : positive) (c : Z) (K H t0 s1 s2 h : sv) (extra : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S87SaS6fVc;A1S71Vc;VK;VH;Vt0;Vs1;Vs2;A6S81S9S16S0A1S14S2SfS2S65S13S2A1A3S14S2S86S14S2S29Vc;Vh;A2Vextra;A3A3A3S14S3Vfacts;S14S3SfS3S6S5PcA1S1S4bVc;A1A1A2S13S3A1A3S5cA3A3Vnx;S17A9S13S12S0S0A2A1A2").

Definition X0 (c : Z) : axst := ltac2:(tb__ "0|1|
S12S12S0S0A2M0S0A2S20Lx;S6eVc;A1G0S0G0S20Lp;R2S0S0S59S7bVc;S1S57Vc;A1A1S22R2R1R3S22S13S2A1S13S3A1AaLs1;Lt0;X12x1Ls2;Lp;X12x1").

Definition F_K (c : Z) : list sprop := ltac2:(tb__ "0|0|
SfS3S6S1Z2A1S26A2SfS3S6S26S1S57Vc;A1A1A2S13S3A1A3A3").
Definition Cgen (nx : positive) (c : Z) (extra : list sobj) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S59Vnx;Vc;S26S25S5Pa0A1S5Pa1A1S5Pa2A1S22Vextra;Vfacts;Aa").

Definition POS (c : Z) : sv := ltac2:(tb__ "0|0|
S4S1fS25S1S55Vc;A1A1A3").
Definition flagaddr (c : Z) : sv := ltac2:(tb__ "0|0|
S4S1dS4S1dS21S1S5bVc;A1A1A3S5dVc;A1A3").
Definition O_flagc (c : Z) (b : Z) : sobj := ltac2:(tb__ "0|3|
S1cS5eVc;A1Z0M0Z1SfS12S12S1aS11A2M1S0A2M2S10G1S0S10S1aS11G0U1A4S1Vb;A1A4S13G2A1A3A4").
Definition ffx (c : Z) : sv := ltac2:(tb__ "0|3|
S15S0L_;S78Vc;Z0A2S4S1dS4S1dS21S1S4dA1A3M0S4S1eS5dVc;A1M1S1Z6M2A1A3A3S4S1dG0S4S1dS4S1eG1S1S76G2Vc;A2A1A3S1S77Vc;S79Z2Z14A2A2A1A3A3X15x2").
Definition O_frame (c : Z) (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|0|
S1cS58Vc;A1Z0S74S4bVc;A1Z8A2Vcs;A4").
Definition O_flagw (c : Z) (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|1|
S1cS58Vc;A1S74S4bVc;A1M0Z8A2G0Vcs;A4").
Definition O_fshadow (c : Z) (cs : list (Z * nat * sv)) : sobj := ltac2:(tb__ "0|0|
S1cS4S1dS7fS58Vc;A1A1S80A3Z0S75S4bVc;A1Z8A2Vcs;A4").
Definition F_found (c : Z) : list sprop := ltac2:(tb__ "0|0|
S7eVhi;S58Vc;A1S4bVc;A1A3").

Definition Cbusy (c : Z) : axst := ltac2:(tb__ "0|0|
S60S7bVc;SfS2S5aVc;Z1A2S13S2A1A3S56Vc;A1A4").
Definition busy_scratch (c : Z) : sv * sv * sv := ltac2:(tb__ "0|0|
S10S12S0S0A2S0S10S0S0S1Z1A1S5eVc;A1A4S5dVc;A1A4").
Definition Ebusy (c : Z) : axst := ltac2:(tb__ "0|2|
S12S12S0S0A2M0S0A2S20Lx;S66Vc;A1G0S0G0S20Lp;R2S0S0S59S7bVc;S4S1dS26S1N1A1A3S4S1dS25S1Z1M1A1A3R2R1R3S22SfS2S5aVc;G1A2S13S2A1A3S56Vc;A1AaLs1;Lt0;X12x1Ls2;Lp;X12x1").

Definition Ebusy0 (c : Z) : axst := ltac2:(tb__ "0|1|
S12S12S0S0A2M0S0A2S20Lx;S66Vc;A1G0S0G0S20Lp;R2S0S0S59S7bVc;S4S1dS26S1N1A1A3S4S1dS25S1Z1A1A3R2R1R3S22S13S2A1S56Vc;A1AaLs1;Lt0;X12x1Ls2;Lp;X12x1").

Definition Cfree (c : Z) : axst := ltac2:(tb__ "0|1|
S60S2aVc;SfS2S5aVc;Z0A2SfS2S63Vc;S13S12S12S1aS11A2S0A2A1M0A2SfS2S62Vc;G0A2SfS2S64Vc;G0A2S13S2A1A3A3A3A3S14S3S56Vc;A1S61Vc;A1A3A4").
Fixpoint zero_cells (k : nat) : list (Z * nat * sv) :=
  match k with O => [] | S k' => (8 * Z.of_nat k', 8%nat, SLit 0) :: zero_cells k' end.
Definition ret_regs (c : Z) : list sv := ltac2:(tb__ "0|1|
S82S84S7cA1SfS12S11S0A2M0S10S11S0U4S1S27A1A4SfG0S10S11S0UaS58Vc;A1A4S13G0A1A3A3A2").
Definition Efree_objs (c : Z) : list sobj := ltac2:(tb__ "0|8|
S14S2SfS2S65S13S2A1M0A3S14S2S86S14S2S29Vc;S4S1dS25S1Z1M1A1A3A2SfS2S5aVc;G1A2SfS2S63Vc;SfS12S12S1aS11A2M2S0A2M3S10G2S0S10S1aS11Z18U8M4A4S5PaA1A4S13G3A1M5A3A2SfS2S62Vc;SfG3S10G2S0S10S1aS11S74S4bVc;A1M6Z8M7A2G4A4S5eVc;A1A4G5A3A2SfS2S64Vc;S73S7aS75S75G6G7A2G7A2A1A1A2G0A3A3A3A3A3A3A3").
Definition Efree (c : Z) : axst := ltac2:(tb__ "0|0|
S87SaS8aS88Vc;A2S72Vc;A1S81S9S16S0A1S6bVc;A1S14S3S14S3S56Vc;A1S61Vc;A1A3S14S3SfS3S6S5PcA1S1S4bVc;A1A1A2S13S3A1A3S5cA3A3S2aS17A9S13S12S0S0A2A1A2").

Definition loopheads : list Z := ltac2:(tb__ "0|0|
SfS1aZ4798cSfS1aZ47b10SfS1aZ47ca0SfS1aZ47e3cSfS1aZ47fe8SfS1aZ482a8S13S1aA1A3A3A3A3A3A3").

Definition sm_certs (c : Z) : bool := ltac2:(tb__ "0|1|
S18S18S85S7dU320S5fS7cSfS20S6cVc;A1S13S20A1M0A3SfS20S6dVc;A1G0A3A6S85S7dUc8S5fS7cSfS20S67Vc;A1G0A3SfS20S69Vc;A1G0A3A6A2S85S7dU190S5fS7cSfS20S68Vc;A1G0A3SfS20S6aVc;A1G0A3A6A2").
End Win.

Lemma sm_certs_1 : forall hi, sm_certs hi 1 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sm_certs_0 : forall hi, sm_certs hi 0 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sm_certs_2 : forall hi, sm_certs hi 2 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sm_certs_3 : forall hi, sm_certs hi 3 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sm_certs_5 : forall hi, sm_certs hi 5 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sm_certs_6 : forall hi, sm_certs hi 6 = true. Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertStackMalloc.

