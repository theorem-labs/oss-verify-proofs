(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_019.   (* [comment removed for export] *)
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "true"; "nil"; "bool"; "Some"; "list"; "option"; "false"; "prod"; "length"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SAlu"; "ss_objs"; "cell"; "SVar"; "sstate"; "SPUle"; "mkObj"; "SExt"; "DUnknown"; "ss_facts"; "DImage"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "swf"; "ob_dflt"; "odefault"; "ss_pc"; "ss_regs"; "SPAlign"; "ob_cells"; "DZero"; "mkCell"; "sprop_below"; "ss_fregs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "entailsA"; "mkAX"; "mkLeafA"; "ax_setS"; "axwf"; "cell_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start7States"; "C18e"; "JPC18"; "J18S"; "K18S"; "XB18"; "o18ssp"; "o18win"; "sJ18"; "C18"; "E18g"; "R18"; "SP18"; "T18c1"; "U18b"; "U18c"; "s18"; "AUXV18"; "C18a"; "C18b"; "C18c"; "C18d"; "C18d'"; "J18"; "L18a"; "T18b"; "T18c"; "myregs18"; "ogrp18c"; "I18af"; "I18bf"; "I18cf"; "L18b"; "L18c"; "X18"; "XE18"; "XL18"; "bytes18"; "o18errno"; "o18ssp_m"; "refact18"; "EV18"; "I18a"; "I18b"; "I18c"; "K18a"; "o18ssp_s"; "oarea18b"; "oarea18c"; "owin18"; "E18b"; "F18"; "odummy18"; "splits18"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface"; "Pre_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "move_obj_last"; "obj_to_unknown"; "split_chain"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_postA3"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post"; "P_null0"; "P_null1"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates"; "E18"; "MALLOC_ENTRY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.MuslMalloc40Post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start4States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition AUXV18 : sv := ltac2:(tb__ "0|1|
S14S72S14S72S14S72S17P1A1S14S74S17P2A1S11Z3A1M0A3A3S14S74S17P3A1G0A3A3S11Z18A1A3").
Definition SP18 : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-240)).
Definition XB18 : sv := SVar 84%positive.
Definition XL18 : sv := SVar 85%positive.
Definition XE18 : sv := SAlu ALU_ADD XB18 XL18.
Definition F18 : list sprop := ltac2:(tb__ "0|4|
S0S13S28P54Z6M0A2S0S13S28P55G0A2S0S13S19S14S72S3eS11Z200A1A3S45A2S0S13S19S45S5cA2S0S13S19S3eS17P6A1M1A2S0S13S19S14S72G1S11Z10A1A3S5cA2S0S13S19S5dS11S81Z2M2Z28A2A1A2S0S13S19S11Z7fff7f000000A1S3eA2S0S13S19S3eS11S81G2Z30A2A1A2S0S13S19S5cS11S81G2Z2fA2M3A1A2S0S13S19S14S72S45S11Z140A1A3G1A2S0S13S19S14S72S45S11Z40A1A3S4aA2S0S13S19S11Z7fff80000000A1S4aA2S0S13S19S4aS11S82G3S81G2Z16A2A2A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X18 : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S2S10S10S3eS5dA4S4G0A1A3").

Definition E18b : sstate := Eval vm_compute in
  (let St := ax_S E18 in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 86%positive (ss_lenient St)).
Definition E18g : sstate := Eval vm_compute in
  (let St := ax_S E18 in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (F18 ++ ss_facts St) 86%positive (ss_lenient St)).
Lemma sd18 : ltac2:(tb__ "0|4|
SfSeS8SaS7SaS10S10A2M0A1M1S7S13A1M2A2M3A1S76S6bS43A2S6G3S2G1G2S4G0A1S6cA4A2A3SfSeS5S23S43A1S3A3SeS2eS22S43A1P56A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition splits18 : list (nat * sv) := ltac2:(tb__ "0|4|
S0SaS1S10A2M0S2S1S10U16M1S11Nbf0A1A4S0G0S2S1S10U17M2S11Nf0A1A4S0G0S2S1S10UeS11Z624514A1A4S0G0S2S1S10UfS11Z624518A1A4S0G0S2S1S10U10S11Z6445f8A1A4S0G0S2S1S10U11S11Z644600A1A4S0G0S2S1S10U12S11Z64484bA1A4S0G0S2S1S10U13S11Z64484cA1A4S0G0S2S1S10U14S11Z644850A1A4S0G0S2S1S10U15S11Z644858A1A4S0G0S2S1S10G1S11Z644878A1A4S0G0S2S1S10G2S11Z644880A1A4S0G0S2S1S10U18S11Z6448c0A1A4S0G0S2S1S10U19S11Z644c68A1A4S0G0S2S1S10U1aS11Z645510A1A4S0G0S2S1S10U1bS11Z645518A1A4S0G0S2S1S10U1cS11Z645dd8A1A4S0G0S2S1S10U1dS11Z645de8A1A4S0G0S2S1S10UaM3S11Zf20d8A1A4S0G0S2S1S10UbS11Zf20daA1A4S0G0S2S1S10U9S11Ze9ac8A1A4S0G0S2S1S10G3S11Ze9af8A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C18a : sstate := Eval vm_compute in (match split_chain E18g splits18 with Some St => St | None => E18g end).
Lemma split18_ok : ltac2:(tb__ "0|0|
SeS8S18A1S7cS43S6eA2S6S18S4bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition odummy18 : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1M0G0G0S4S16A1S2aA5").
Definition ob18 (St : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S6fS12Vi;S15VSt;A1S6dA4").

Definition o18errno : sobj := Eval vm_compute in ob18 C18a 19.
Definition C18b : sstate := Eval vm_compute in replace_obj_at C18a 19 (obj_to_unknown o18errno).
Lemma C18b_facts : ltac2:(tb__ "0|2|
SfSeS8S12A1S7dS12S15S4bA1U13M0A3S6S12S5fA2A3SfSeS25S24S5fA1S1eA3SfSeS5S75S4bS79S4bG0S7bS5fA1A3M1A2S3A3SeS18G1S4cA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18ssp : sobj := Eval vm_compute in ob18 C18b 21.
Definition es18 : list sv := ltac2:(tb__ "0|2|
S0S10S1bS9Q8M0S17P9A1M1A3S0S10S11Z0A1S0S10S1bS9G0S14S73G1S11Z10A1A3A3S0S10S1bS9G0S14S73G1S11Z18A1A3A3S0S10S1bS9G0S14S73G1S11Z20A1A3A3S0S10S1bS9G0S14S73G1S11Z28A1A3A3S0S10S1bS9G0S14S73G1S11Z30A1A3A3S0S10S14S73G1S11Z38A1A3S4S10A1A3A3A3A3A3A3A3A3").
Definition bytes18 : list cell := byte_cells 0x6445f8 es18.
Definition EV18 : sv := SAlu ALU_AND (SVar 9%positive) (SLit 18446744073709486335).
Definition o18ssp_s : sobj := ltac2:(tb__ "0|0|
S1aS11Z0A1S11Z6445f8A1S11Z644600A1S5eS1eA5").
Definition C18c : sstate := Eval vm_compute in replace_obj_at C18b 21 o18ssp_s.
Definition o18ssp_m : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1S11Z6445f8A1M0S11Z644600A1S0S16S2bG0Z8S62A3S4S16A1A3S1eA5").
Definition C18d : sstate := Eval vm_compute in replace_obj_at C18c 21 o18ssp_m.
Definition C18d' : sstate := Eval vm_compute in replace_obj_at C18d 21 (obj_to_unknown o18ssp_m).
Lemma C18c_facts : ltac2:(tb__ "0|4|
SfSeS8S12A1S7dS12S15S4cA1U15M0A3S6S12S3fA2A3SfSeS10S1fS3fA1S11Z0A1A3SfSeS10S21S3fA1S11Z6445f8A1A3SfSeS10S20S3fA1S11Z644600A1A3SfSeS25S24S3fA1S1eA3SfSeS5S7fS16S16S7eS16S39R1A1M1S5eA3Lc;S29S3fA1M2A3S3A3SfSeS5S7fS16S16S7eS16G1G2A3Lc;S5eA3S3A3SfSeS5S75S4cS79S4cG0S67A3M3A2S3A3SeS18G3S4dA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18d_facts : ltac2:(tb__ "0|4|
SfSeS8S12A1M0S7dS12S15S4dA1U15M1A3S6S12S67A2A3SfSeS5S75S4dS79S4dG1S60A3M2A2S3A3SfSeS18G2S4eA3SfSeG0S7dS12S15S4eA1G1A3S6S12S60A2A3SfSeS5S75S4eS79S4eG1S7bS60A1A3M3A2S3A3SeS18G3S4fA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18win : sobj := Eval vm_compute in ob18 C18d' 43.
Definition owin18 : sobj := ltac2:(tb__ "0|0|
S1aS17P1A1S11Nbf0A1S11Nf0A1S4S16A1S1cA5").
Definition C18e : sstate := Eval vm_compute in replace_obj_at C18d' 43 owin18.
Lemma C18e_facts : ltac2:(tb__ "0|3|
SfSeS8S12A1S7dS12S15S4fA1U2bM0A3S6S12S40A2A3SfSeS25S24S40A1M1S1cA3SfSeS12S1aS1fS40A1S21S40A1S20S40A1S80S16S16S9L_;S29S40A1A3G1A5S6aA3SfSeS5S75S4fS79S4fG0S6aA3M2A2S3A3SeS18G2S3aA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C18 : axst := ltac2:(tb__ "0|0|
S35S3aS5bS11S83A1A3").
Lemma C18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3aA1S8fA3SfSeS2eS22S3aA1P56A3SfSeS1SbS12S15S3aA1A2U30A3SfSeS5S23S3aA1S3A3SfSeS7S13A1S1dS3aA1S1dS43A1A3SeS7S10A1S27S3aA1S27S32S8eA1A1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18e_facts_below : ltac2:(tb__ "0|0|
SeS5S7fS13S2cP56A1S1dS3aA1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition myregs18 : list sv := ss_regs C18e.
Definition s18 : wsub := ltac2:(tb__ "0|8|
ScSaS2eS10A2M0S0G0S2S2eS10PaM1S45A4S0G0S2S2eS10PbS6fS10U1M2S54S11Z0A1M3A4A4S0G0S2S2eS10PdS6fS10UbM4S54G3A4A4S0G0S2S2eS10PeS6fS10UcM5S54G3A4A4S0G0S2S2eS10PfS62A4S0G0S2S2eS10P10S4aA4S0G0S2S2eS10P11S17P6A1A4S0G0S2S2eS10P12S17P7A1A4S0G0S2S2eS10P13S17P8A1A4S0G0S2S2eS10P34S3eA4S0G0S2S2eS10P35S5dA4S0G0S2S2eS10P36S17P9A1A4S0G0S2S2eS10P37S17G1A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3ScG0S70S1G0S1S2S2eS10S8dS88U14R1A2A1S6fS10R1S54G3A4A4Lr;S95S1S7S1A1S97S1A1S1S94SdS7eS1S93R1A1S0S1G2S0S1U2S0S1UaS0S1G4S0S1G5S4S1A1A3A3A3A3A3A3A1M6A1Lr;S1S96G6A1Lx;S71U0U20A2M7A6A4S70S1G0S1S2S2eS10S8dS88U3cR1A2A1S6fS10R1S2dS3aA1G3A4A4Lr;G7A4A3A3").
Definition R18 : list sobj := Eval vm_compute in (match entails_frA C18 Pre_M s18 with Some R => R | None => [] end).
Lemma ent18 : ltac2:(tb__ "0|1|
SeS8S7S12A1M0A1S92S42S78S49A3S6G0S44A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk18 : ltac2:(tb__ "0|0|
SeS5S91S42S78S49S44S0S30S89S0S30S8aS0S30S8bS4S30A1A3A3A3A5S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R18_len : length R18 = 34%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition I18a : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_null0 C18 R18 []).
Definition I18b : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_null1 C18 R18 []).
Definition I18c : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_ok C18 R18 []).
Lemma I18_eq : ltac2:(tb__ "0|1|
SfSeS30S87S49S78S89S42S44S4SaS10S10A2A1M0A6S63A3SfSeS30S87S49S78S8aS42S44G0A6S64A3SeS30S87S49S78S8bS42S44G0A6S65A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition refact18 (A : axst) : axst := ltac2:(tb__ "0|0|
S90VA;ScS13S1dS32VA;A1A1S1dS3aA1A3A2").
Definition I18af : axst := Eval vm_compute in refact18 I18a.
Definition I18bf : axst := Eval vm_compute in refact18 I18b.
Definition I18cf : axst := Eval vm_compute in refact18 I18c.
Lemma I18f_eq : ltac2:(tb__ "0|0|
SfSeS30S61S63A1S56A3SfSeS30S61S64A1S57A3SeS30S61S65A1S58A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition JPC18 : Z := 0x657dc.
Definition run18a__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S56S3A5").
Local Strategy expand [run18a__R].
Definition L18a : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (leaf1 I18af (ro1__))) run18a__R).
Definition run18b__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S57S3A5").
Local Strategy expand [run18b__R].
Definition L18b : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 I18bf (ro2__))) run18b__R).
Definition run18c__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S58S3A5").
Local Strategy expand [run18c__R].
Definition L18c : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => (leaf1 I18cf (ro3__))) run18c__R).
Lemma run18a : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S56S3A5S6G0S0S31S36S51S85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18a__R <: run18a__R = Some [mkLeafA L18a RsCut]). Qed.
Lemma run18b : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S57S3A5S6G0S0S31S36S59S85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18b__R <: run18b__R = Some [mkLeafA L18b RsCut]). Qed.
Lemma run18c : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S58S3A5S6G0S0S31S36S5aS85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18c__R <: run18c__R = Some [mkLeafA L18c RsCut]). Qed.

Definition T18b : sstate := Eval vm_compute in move_obj_last (ax_S L18b) 14.
Definition U18b : axst := Eval vm_compute in ax_setS L18b (set_objs T18b (firstn 48 (ss_objs T18b))).
Definition oarea18b : sobj := Eval vm_compute in nth 48 (ss_objs T18b) odummy18.
Lemma T18b_facts : ltac2:(tb__ "0|3|
SfSeS18S7aS32S59A1M0UeA2S52A3SfSeS5S75G0S52A2S3A3SfSeS1SbS12S15G0A1A2U31A3SfSeS7S12A1S15S52A1ScS12S15S32S47A1A1M1S0S12S68S4S12A1A3A3A3SfSeS30S37S59S86S52G1A2A2S47A3SeS12S68S1aS14S72S17P94A1S11Z1000A1M2A3S11Z0A1G2S4S16A1S1cA5A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T18c1 : sstate := Eval vm_compute in move_obj_last (ax_S L18c) 14.
Definition T18c : sstate := Eval vm_compute in move_obj_last T18c1 14.
Definition U18c : axst := Eval vm_compute in ax_setS L18c (set_objs T18c (firstn 48 (ss_objs T18c))).
Definition oarea18c : sobj := Eval vm_compute in nth 48 (ss_objs T18c) odummy18.
Definition ogrp18c : sobj := Eval vm_compute in nth 49 (ss_objs T18c) odummy18.
Lemma T18c_facts : ltac2:(tb__ "0|6|
SfSeS18S7aS32S5aA1M0UeM1A2S46A3SfSeS5S75G0S46A2S3A3SfSeS1SbS12S15G0A1A2U32M2A3SfSeS18S7aS46G1A2S53A3SfSeS5S75S46S53A2S3A3SfSeS1SbS12S15S46A1A2G2A3SfSeS7S12A1S15S53A1ScS12S15S32S48A1A1M3S0S12S69S0S12S55S4S12A1A3A3A3A3SfSeS30S37S5aS86S53G3A2A2S48A3SfSeS12S69S1aS14S72S17P94A1S11Z1000A1M4A3S11Z0A1M5G4S4S16A1S1cA5A3SfSeS10S1fS55A1S17P95A1A3SfSeS10S21S55A1G5A3SeS10S20S55A1G4A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ounk18 (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1aS1fVo;A1S21Vo;A1S20Vo;A1S4S16A1S1cA5").
Definition J18objs2 : list sobj := Eval vm_compute in
  (let l := ss_objs (ax_S L18a) in
   let o i := nth i l odummy18 in
   [o 14; o 12; o 13; o 15; o 16; o 8; o 17; o 9; o 18;
    o 19; o 11; o 20; o 21; o 10; o 22; o 23; o 24; o 25;
    o 26; o 6; o 27; o 5; o 28; o 2; o 29; o 3; o 30; o 4; o 31; o 1; o 32; ounk18 (o 33); o 34; o 7; o 35;
    o 36; o 37; o 38; o 39; o 40; o 41; o 42;
    o 43; owin18; o 44;
    o 45; o 46; o 47]%nat).
Definition J18S : sstate := Eval vm_compute in
  (let St := ax_S L18a in
   mkSS JPC18 (list_set (list_set (list_set (ss_regs St) 10 (SVar 156%positive)) 11 (SVar 157%positive)) 13 (SVar 158%positive))
        (ss_fregs St) (ss_fcsr St) (ss_resv St) J18objs2 (ss_facts C18e) 159%positive (ss_lenient St)).
Definition J18 : axst := ltac2:(tb__ "0|0|
S35S3cS5bS11S83A1A3").
Definition sJ18 (L : axst) : wsub := ltac2:(tb__ "0|3|
S0SaS2eS10A2M0S2S2eS10P9cS6fS10UaS27S32VL;A1A1M1S11Z0A1M2A4A4S0G0S2S2eS10P9dS6fS10UbG1G2A4A4S0G0S2S2eS10P9eS6fS10UdG1G2A4A4S4G0A1A3A3A3").
Lemma entJ18a : ltac2:(tb__ "0|0|
SeS5S34S51S50S41S51A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18b : ltac2:(tb__ "0|0|
SeS5S34S47S50S41S47A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18c : ltac2:(tb__ "0|0|
SeS5S34S48S50S41S48A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sJ18_id : ltac2:(tb__ "0|1|
SfSeS5S84S41S51A1P9cM0A2S3A3SfSeS5S84S41S47A1G0A2S3A3SeS5S84S41S48A1G0A2S3A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma J18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3cA1S3bA3SfSeS2eS22S3cA1P9fA3SfSeS1SbS12S15S3cA1A2U30A3SfSeS5S23S3cA1S3A3SeS5S38S50A1S3A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K18a : sstate := Eval vm_compute in (match merge_objs_at J18S 42 with Some St => St | None => J18S end).
Definition K18S : sstate := Eval vm_compute in (match merge_objs_at K18a 42 with Some St => St | None => K18a end).
Lemma K18_eq : ltac2:(tb__ "0|2|
SfSeS8S18A1M0S8cS3cU2aM1A2S6S18S66A2A3SeG0S8cS66G1A2S6S18S3dA2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition K18 : axst := ltac2:(tb__ "0|0|
S35S3dS5bS11S83A1A3").
Lemma K18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3dA1S3bA3SfSeS2eS22S3dA1P9fA3SfSeS1SbS12S15S3dA1A2U2eA3SeS5S23S3dA1S3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
